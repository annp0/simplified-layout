(* SASS instructions as the emitter builds them: the text cuobjdump would
   print, without a control word, plus what the scheduler needs to know —
   which registers are written, read, or read late (asynchronously, by the
   memory pipe), and the latency class of the result. *)

type reg =
  | R of int
  | UR of int
  | P of int
  | UP of int
  | Tok of int (* an ordering token: memory fences, the tensor-core issue queue *)

type lat =
  | Fixed of int (* result usable this many cycles after issue *)
  | Variable (* completes on a scoreboard *)

type branch =
  [ `No
  | `Bra of string
  | `Exit
  ]

type insn =
  { text : string
  ; guard : string (* "" or "@P3 " / "@!P3 " *)
  ; defs : reg list
  ; uses : reg list
  ; late_uses : reg list (* read by the memory pipe after issue *)
  ; lat : lat
  ; src_hold : int (* cycles after issue during which [uses] are still being read *)
  ; pipe : string
  ; branch : branch
  ; min_stall : int (* cycles before the next issue, for instructions whose effect is deferred *)
  ; drain : bool (* waits for every store issued so far to have read its data: fences and barriers *)
  ; force_rb : int option (* a read scoreboard named by a later wait, so it cannot float *)
  ; force_wb : int option (* a write scoreboard named by an earlier wait, likewise *)
  }

type item =
  | Label of string
  | I of insn

type t = { mutable items : item list }

let create () = { items = [] }
let push b it = b.items <- it :: b.items
let items b = List.rev b.items
let label b l = push b (Label l)

let mk ?(guard = "") ?(defs = []) ?(uses = []) ?(late = []) ?(lat = Fixed 6) ?(hold = 0)
    ?(pipe = "alu") ?(branch = `No) ?(min_stall = 0) ?(drain = false) ?force_rb ?force_wb text =
  { text; guard; defs; uses; late_uses = late; lat; src_hold = hold; pipe; branch; min_stall; drain; force_rb; force_wb }

let regs r n = List.init n (fun i -> R (r + i))
let urs u n = List.init n (fun i -> UR (u + i))
let hex n = if n < 0 then Printf.sprintf "-0x%x" (-n) else Printf.sprintf "0x%x" n
let addr base imm = if imm = 0 then Printf.sprintf "[R%d.64]" base else Printf.sprintf "[R%d.64+%s]" base (hex imm)
let pf = Printf.sprintf

(* constant bank / special registers *)
let ldc b d off = push b (I (mk ~defs:[ R d ] ~lat:Variable (pf "LDC R%d, c[0x0][%s]" d (hex off))))
let s2r_tid b d = push b (I (mk ~defs:[ R d ] ~lat:Variable (pf "S2R R%d, SR_TID.X" d)))
let ldcu64 b u off = push b (I (mk ~defs:(urs u 2) ~lat:Variable (pf "LDCU.64 UR%d, c[0x0][%s]" u (hex off))))
let ldcu128 b u off = push b (I (mk ~defs:(urs u 4) ~lat:Variable (pf "LDCU.128 UR%d, c[0x0][%s]" u (hex off))))

(* global memory; the descriptor lives in UR4:UR5 *)
let ldg b d ~base ~imm =
  push b (I (mk ~defs:[ R d ] ~uses:(urs 4 2) ~late:(regs base 2) ~lat:Variable ~pipe:"lsu"
               (pf "LDG.E R%d, desc[UR4]%s" d (addr base imm))))

let stg64 b ~base ~imm ~data =
  push b (I (mk ~uses:(urs 4 2) ~late:(regs base 2 @ regs data 2) ~lat:Variable ~pipe:"lsu"
               (pf "STG.E.64 desc[UR4]%s, R%d" (addr base imm) data)))

(* integer ALU; results usable after 6 cycles (conservative) *)
let alu = Fixed 6

let iadd3_imm b d ~carry a imm =
  push b (I (mk ~defs:[ R d; P carry ] ~uses:[ R a ] ~lat:alu (pf "IADD3 R%d, P%d, PT, R%d, %s, RZ" d carry a (hex imm))))

let iadd3_ur b d ~carry a u =
  push b (I (mk ~defs:[ R d; P carry ] ~uses:[ R a; UR u ] ~lat:alu (pf "IADD3 R%d, P%d, PT, R%d, UR%d, RZ" d carry a u)))

let imad_x_r b d hi p =
  push b (I (mk ~defs:[ R d ] ~uses:[ R hi; P p ] ~lat:alu (pf "IMAD.X R%d, RZ, RZ, R%d, P%d" d hi p)))

let imad_x_ur b d hi p =
  push b (I (mk ~defs:[ R d ] ~uses:[ UR hi; P p ] ~lat:alu (pf "IMAD.X R%d, RZ, RZ, UR%d, P%d" d hi p)))

(* d = a * imm + c *)
let imad b d a imm c =
  push b (I (mk ~defs:[ R d ] ~uses:[ R a; R c ] ~lat:alu (pf "IMAD R%d, R%d, %s, R%d" d a (hex imm) c)))

let imad_rz b d a imm =
  push b (I (mk ~defs:[ R d ] ~uses:[ R a ] ~lat:alu (pf "IMAD R%d, R%d, %s, RZ" d a (hex imm))))

let mov_rz b d = push b (I (mk ~defs:[ R d ] ~lat:alu (pf "MOV R%d, RZ" d)))
let cs2r b d = push b (I (mk ~defs:(regs d 2) ~lat:alu (pf "CS2R R%d, SRZ" d)))

let lop3_and b d a imm =
  push b (I (mk ~defs:[ R d ] ~uses:[ R a ] ~lat:alu (pf "LOP3.LUT R%d, R%d, %s, RZ, 0xc0, !PT" d a (hex imm))))

let shf_r b d a sh =
  push b (I (mk ~defs:[ R d ] ~uses:[ R a ] ~lat:alu (pf "SHF.R.U32.HI R%d, RZ, %s, R%d" d (hex sh) a)))

let viadd b d a imm = push b (I (mk ~defs:[ R d ] ~uses:[ R a ] ~lat:alu (pf "VIADD R%d, R%d, %s" d a (hex imm))))

(* predicate for a branch: 13 cycles, as the branch resolves it *)
let isetp_lt_u32 b p a imm =
  push b (I (mk ~defs:[ P p ] ~uses:[ R a ] ~lat:(Fixed 13) (pf "ISETP.LT.U32.AND P%d, PT, R%d, %s, PT" p a (hex imm))))

(* m16n8k16 f16 -> f32: D(4) = A(4) * B(2) + C(4) *)
let hmma b ~d ~a ~bb ~c =
  push b (I (mk ~defs:(regs d 4) ~uses:(regs a 4 @ regs bb 2 @ regs c 4) ~lat:(Fixed 24) ~hold:4 ~pipe:"hmma"
               (pf "HMMA.16816.F32 R%d, R%d, R%d, R%d" d a bb c)))

let bra b ?(neg = false) p l =
  push b (I (mk ~guard:(pf "@%sP%d " (if neg then "!" else "") p) ~uses:[ P p ] ~branch:(`Bra l) (pf "BRA %s" l)))

let exit b = push b (I (mk ~branch:`Exit ~drain:true "EXIT"))

(* ---- the tcgen05 path: uniform datapath, shared memory, mbarriers, TMEM ---- *)

let s2ur_cta b u = push b (I (mk ~defs:[ UR u ] ~lat:Variable (pf "S2UR UR%d, SR_CgaCtaId" u)))
let umov b u imm = push b (I (mk ~defs:[ UR u ] ~lat:alu (pf "UMOV UR%d, %s" u (hex imm))))

let uiadd3 b d a imm =
  push b (I (mk ~defs:[ UR d ] ~uses:[ UR a ] ~lat:alu (pf "UIADD3 UR%d, UPT, UPT, UR%d, %s, URZ" d a (hex imm))))

let uiadd3_uu b d a c =
  push b (I (mk ~defs:[ UR d ] ~uses:[ UR a; UR c ] ~lat:alu (pf "UIADD3 UR%d, UPT, UPT, UR%d, UR%d, URZ" d a c)))

let uiadd3_neg b d a imm =
  push b (I (mk ~defs:[ UR d ] ~uses:[ UR a ] ~lat:alu (pf "UIADD3 UR%d, UPT, UPT, -UR%d, %s, URZ" d a (hex imm))))

let ushf_l b d a sh = push b (I (mk ~defs:[ UR d ] ~uses:[ UR a ] ~lat:alu (pf "USHF.L.U32 UR%d, UR%d, %s, URZ" d a (hex sh))))
let ushf_r b d a sh = push b (I (mk ~defs:[ UR d ] ~uses:[ UR a ] ~lat:alu (pf "USHF.R.U32.HI UR%d, URZ, %s, UR%d" d (hex sh) a)))

let ulop3_and b d a imm =
  push b (I (mk ~defs:[ UR d ] ~uses:[ UR a ] ~lat:alu (pf "ULOP3.LUT UR%d, UR%d, %s, URZ, 0xc0, !UPT" d a (hex imm))))

let ulop3_or b d a imm =
  push b (I (mk ~defs:[ UR d ] ~uses:[ UR a ] ~lat:alu (pf "ULOP3.LUT UR%d, UR%d, %s, URZ, 0xfc, !UPT" d a (hex imm))))

let ulop3_not b d a = push b (I (mk ~defs:[ UR d ] ~uses:[ UR a ] ~lat:alu (pf "ULOP3.LUT UR%d, URZ, UR%d, URZ, 0x33, !UPT" d a)))

(* d = (a << sh) + c *)
let ulea b d a c sh = push b (I (mk ~defs:[ UR d ] ~uses:[ UR a; UR c ] ~lat:alu (pf "ULEA UR%d, UR%d, UR%d, %s" d a c (hex sh))))
let r2ur b u r = push b (I (mk ~defs:[ UR u ] ~uses:[ R r ] ~lat:(Fixed 13) (pf "R2UR UR%d, R%d" u r)))
let mov_ur b d u = push b (I (mk ~defs:[ R d ] ~uses:[ UR u ] ~lat:alu (pf "IMAD.U32 R%d, RZ, RZ, UR%d" d u)))
let lea_ur b d a u sh = push b (I (mk ~defs:[ R d ] ~uses:[ R a; UR u ] ~lat:alu (pf "LEA R%d, R%d, UR%d, %s" d a u (hex sh))))
let mov_imm b d imm = push b (I (mk ~defs:[ R d ] ~lat:alu (pf "MOV R%d, %s" d (hex imm))))
let shf_l b d a sh = push b (I (mk ~defs:[ R d ] ~uses:[ R a ] ~lat:alu (pf "SHF.L.U32 R%d, R%d, %s, RZ" d a (hex sh))))
let lop3_xor b d a c = push b (I (mk ~defs:[ R d ] ~uses:[ R a; R c ] ~lat:alu (pf "LOP3.LUT R%d, R%d, R%d, RZ, 0x3c, !PT" d a c)))
let iadd3 b d a c = push b (I (mk ~defs:[ R d ] ~uses:[ R a; R c ] ~lat:alu (pf "IADD3 R%d, PT, PT, R%d, R%d, RZ" d a c)))
let iadd3_c b d a imm = push b (I (mk ~defs:[ R d ] ~uses:[ R a ] ~lat:alu (pf "IADD3 R%d, PT, PT, R%d, %s, RZ" d a (hex imm))))

let isetp_ne_u32 b p a imm =
  let rhs = if imm = 0 then "RZ" else hex imm in
  push b (I (mk ~defs:[ P p ] ~uses:[ R a ] ~lat:(Fixed 13) (pf "ISETP.NE.U32.AND P%d, PT, R%d, %s, PT" p a rhs)))

let jmp b l = push b (I (mk ~branch:(`Bra l) (pf "BRA %s" l)))

(* shared memory; addresses are the cluster form (cta << 24 | offset) held in a UR *)
let lds b d ~ur ~imm = push b (I (mk ~defs:[ R d ] ~late:[ UR ur ] ~lat:Variable ~pipe:"lsu" (pf "LDS R%d, [UR%d+%s]" d ur (hex imm))))

let sts b ~width ~r ~ur ~imm ~data =
  let n = width / 32 in
  let suffix = if width = 32 then "" else pf ".%d" width in
  push b (I (mk ~uses:[ UR ur ] ~late:(R r :: regs data n) ~lat:Variable ~pipe:"lsu"
               (pf "STS%s [R%d+UR%d+%s], R%d" suffix r ur (hex imm) data)))

let sts_ur b ~ur ~imm ~data =
  push b (I (mk ~uses:[ UR ur ] ~late:[ R data ] ~lat:Variable ~pipe:"lsu" (pf "STS [UR%d+%s], R%d" ur (hex imm) data)))

let width_suffix = function 32 -> "" | w -> pf ".%d" w

(* a global load of [width] bits into width/32 registers *)
let ldg_w b ~width d ~base ~imm =
  push b (I (mk ~defs:(regs d (width / 32)) ~uses:(urs 4 2) ~late:(regs base 2) ~lat:Variable ~pipe:"lsu"
               (pf "LDG.E%s R%d, desc[UR4]%s" (width_suffix width) d (addr base imm))))

let ldg128 b d ~base ~imm = ldg_w b ~width:128 d ~base ~imm

let stg128 b ~base ~imm ~data =
  push b (I (mk ~uses:(urs 4 2) ~late:(regs base 2 @ regs data 4) ~lat:Variable ~pipe:"lsu"
               (pf "STG.E.128 desc[UR4]%s, R%d" (addr base imm) data)))

(* ordering: token 0 threads the fences and barriers, token 1 the tensor-core issue queue *)
let membar_cta b = push b (I (mk ~late:[ Tok 0 ] ~lat:Variable ~drain:true "MEMBAR.ALL.CTA"))
let fence_view_async b = push b (I (mk ~defs:[ Tok 0 ] ~uses:[ Tok 0 ] ~lat:Variable ~drain:true "FENCE.VIEW.ASYNC.S"))
let bar_sync b = push b (I (mk ~defs:[ Tok 0 ] ~uses:[ Tok 0 ] ~lat:(Fixed 6) ~min_stall:6 ~drain:true "BAR.SYNC.DEFER_BLOCKING 0x0"))

(* a named barrier over a subset of the block: the warps that store share one,
   and the warps that feed the tensor core never arrive at it *)
let bar_sync_n b ~bar ~count =
  push b (I (mk ~defs:[ Tok 0 ] ~uses:[ Tok 0 ] ~lat:(Fixed 6) ~min_stall:6 ~drain:true
               (pf "BAR.SYNC.DEFER_BLOCKING %s, %s" (hex bar) (hex count))))

let bar_addr base imm = if imm = 0 then pf "[UR%d]" base else pf "[UR%d+%s]" base (hex imm)

let syncs_exch b ~base ~imm ~v =
  push b (I (mk ~defs:[ Tok 0 ] ~uses:[ Tok 0 ] ~late:[ UR base; UR v; UR (v + 1) ] ~lat:Variable
               (pf "SYNCS.EXCH.64 URZ, %s, UR%d" (bar_addr base imm) v)))

(* the operands of a spin wait are never rewritten inside the loop, so they
   take no read barrier: one per iteration would flood the scoreboard *)
let syncs_trywait b p ~base ~imm ~parity_reg =
  let rb = match parity_reg with None -> "RZ" | Some r -> pf "R%d" r in
  let uses = match parity_reg with None -> [ UR base ] | Some r -> [ UR base; R r ] in
  push b (I (mk ~defs:[ P p ] ~uses ~lat:Variable
               (pf "SYNCS.PHASECHK.TRANS64.TRYWAIT P%d, %s, %s" p (bar_addr base imm) rb)))

let depbar_sb0 b = push b (I (mk ~lat:alu ~min_stall:4 "DEPBAR.LE SB0, 0x36"))

(* [two] asks the allocator for the CTA PAIR, which is what makes a two-CTA
   MMA work: both CTAs get the same tensor-memory columns, and the accumulator
   the instruction writes half into each lands at one address. *)
(* the allocator's answer is tracked on scoreboard 0, the one the DEPBAR before
   it names -- ptxas pairs the two the same way *)
let utcatomsws_fas ?(two = false) b u =
  push b (I (mk ~defs:[ UP 0; UR u ] ~late:[ UR u ] ~lat:Variable ~force_wb:0
               (pf "UTCATOMSWS%s.FIND_AND_SET.ALIGN UP0, UR%d, UR%d" (if two then ".2CTA" else "") u u)))

let plop3_up b p ~up =
  push b (I (mk ~defs:[ P p ] ~uses:[ UP up ] ~lat:(Fixed 13) (pf "PLOP3.LUT P%d, PT, PT, PT, UP%d, 0x80, 0x8" p up)))

let plop3_up0 b p = push b (I (mk ~defs:[ P p ] ~uses:[ UP 0 ] ~lat:(Fixed 13) (pf "PLOP3.LUT P%d, PT, PT, PT, UP0, 0x80, 0x8" p)))
let nanosleep b = push b (I (mk ~lat:alu ~min_stall:5 "NANOSLEEP 0x64"))
let uvirtcount_dealloc b = push b (I (mk ~lat:alu "UVIRTCOUNT.DEALLOC.SMPOOL 0x80"))
let utcatomsws_and b u = push b (I (mk ~late:[ UR u ] ~lat:Variable (pf "UTCATOMSWS.AND URZ, UR%d" u)))

let utchmma b ~a ~bb ~d ~e ~idesc ~acc =
  push b (I (mk ~defs:[ Tok 1 ] ~uses:[ Tok 1 ] ~late:[ UR a; UR (a + 1); UR bb; UR (bb + 1); UR d; UR e; UR idesc ] ~lat:(Fixed 12) ~min_stall:12
               (pf "UTCHMMA gdesc[UR%d], gdesc[UR%d], tmem[UR%d], tmem[UR%d], idesc[UR%d], %s" a bb d e idesc (if acc then "UPT" else "!UPT"))))

let utcbar b ~mbar = push b (I (mk ~defs:[ Tok 1 ] ~uses:[ Tok 1 ] ~late:[ UR mbar ] ~lat:(Fixed 12) ~min_stall:12 (pf "UTCBAR [UR%d], URZ" mbar)))

let ldtm b d ~n ~addr =
  push b (I (mk ~defs:(regs d n) ~uses:[ UR addr ] ~lat:Variable ~pipe:"lsu" (pf "LDTM.x%d R%d, tmem[UR%d]" n d addr)))

let ushf_l_ur b d a sh = push b (I (mk ~defs:[ UR d ] ~uses:[ UR a; UR sh ] ~lat:alu (pf "USHF.L.U32 UR%d, UR%d, UR%d, URZ" d a sh)))
let ulop3_or_ur b d a c = push b (I (mk ~defs:[ UR d ] ~uses:[ UR a; UR c ] ~lat:alu (pf "ULOP3.LUT UR%d, UR%d, UR%d, URZ, 0xfc, !UPT" d a c)))

(* ---- the pipelined path: TMA, per-stage mbarriers, uniform predicates ---- *)

let s2r_ctaid b d ~axis = push b (I (mk ~defs:[ R d ] ~lat:Variable (pf "S2R R%d, SR_CTAID.%s" d axis)))

let isetp_eq_u32 b p a imm =
  let rhs = if imm = 0 then "RZ" else hex imm in
  push b (I (mk ~defs:[ P p ] ~uses:[ R a ] ~lat:(Fixed 13) (pf "ISETP.EQ.U32.AND P%d, PT, R%d, %s, PT" p a rhs)))

let isetp_lt_u32_imm b p a imm =
  push b (I (mk ~defs:[ P p ] ~uses:[ R a ] ~lat:(Fixed 13) (pf "ISETP.LT.U32.AND P%d, PT, R%d, %s, PT" p a (hex imm))))

let lop3_xor_imm b d a imm =
  push b (I (mk ~defs:[ R d ] ~uses:[ R a ] ~lat:alu (pf "LOP3.LUT R%d, R%d, %s, RZ, 0x3c, !PT" d a (hex imm))))

(* UTMALDG.2D [URg], [URmap]: URg = smem destination, URg+1 = mbarrier, URg+2 = x, URg+3 = y.
   With .MULTICAST the load also names a CTA mask: the slice it fetches lands in
   the shared memory of every CTA of the cluster the mask selects. *)
(* [two] marks a load that feeds a two-CTA MMA: its bytes are reported to the
   pair, so neither CTA can start the MMA until both halves have landed *)
let utmaldg ?(two = false) b ~g ~map =
  push b (I (mk ~late:(urs g 4 @ urs map 2) ~lat:Variable ~min_stall:2
               (pf "UTMALDG.2D%s [UR%d], [UR%d]" (if two then ".2CTA" else "") g map)))

let utmaldg_mc ?guard ?(two = false) b ~g ~map ~mask =
  let gd, gu = match guard with None -> ("", []) | Some u -> (pf "@UP%d " u, [ UP u ]) in
  push b (I (mk ~guard:gd ~uses:gu ~late:(urs g 4 @ urs map 2 @ [ UR mask ]) ~lat:Variable ~min_stall:2
               (pf "UTMALDG.2D.MULTICAST%s [UR%d], [UR%d], UR%d" (if two then ".2CTA" else "") g map mask)))

(* one lane arrives with an expected transaction count / plainly *)
(* the same expect-transaction arrival on another CTA's copy of the barrier *)
let syncs_arrive_tx_red b ~guard ~base ~imm ~tx =
  push b (I (mk ~guard:(pf "@P%d " guard) ~uses:[ P guard ] ~late:[ UR base; R tx ] ~lat:Variable
               (pf "SYNCS.ARRIVE.TRANS64.RED RZ, %s, R%d" (bar_addr base imm) tx)))

let syncs_arrive_tx b ~guard ~base ~imm ~tx =
  push b (I (mk ~guard:(pf "@P%d " guard) ~uses:[ P guard ] ~late:[ UR base; R tx ] ~lat:Variable
               (pf "SYNCS.ARRIVE.TRANS64 RZ, %s, R%d" (bar_addr base imm) tx)))

(* an arrival on another CTA's copy of a barrier: the address carries that
   CTA in its top byte and the arrival is a reduction, which is the form ptxas
   emits for a remote arrive (a remote WAIT is illegal) *)
(* A CTA of a cluster may not leave while a peer can still write its shared
   memory, so the cluster meets once before the exits.  This is what
   barrier.cluster.arrive / barrier.cluster.wait lower to (ref/remarrive.ptx). *)
let cluster_barrier b =
  (* these forms pin their own barrier fields, so they carry no scoreboard of
     their own; draining before each one is what orders them *)
  List.iter
    (fun t -> push b (I (mk ~lat:(Fixed 6) ~drain:true ~min_stall:6 t)))
    [ "MEMBAR.ALL.CTA"; "MEMBAR.ALL.GPU"; "ERRBAR"; "CGAERRBAR"; "UCGABAR_ARV"; "UCGABAR_WAIT"; "CCTL.IVALL" ]

let syncs_arrive_red b ~guard ~base ~imm =
  push b (I (mk ~guard:(pf "@P%d " guard) ~uses:[ P guard ] ~late:[ UR base ] ~lat:Variable
               (pf "SYNCS.ARRIVE.TRANS64.RED.A1T0 RZ, %s, RZ" (bar_addr base imm))))

let syncs_arrive b ~guard ~base ~imm =
  push b (I (mk ~guard:(pf "@P%d " guard) ~uses:[ P guard ] ~late:[ UR base ] ~lat:Variable
               (pf "SYNCS.ARRIVE.TRANS64.A1T0 RZ, %s, RZ" (bar_addr base imm))))

(* a uniform predicate takes as long to become readable as a regular one *)
let uisetp_ne b up a =
  push b (I (mk ~defs:[ UP up ] ~uses:[ UR a ] ~lat:(Fixed 13) (pf "UISETP.NE.U32.AND UP%d, UPT, UR%d, URZ, UPT" up a)))

(* accumulate flag from a uniform predicate register *)
let utchmma_up b ~a ~bb ~d ~e ~idesc ~up =
  push b (I (mk ~defs:[ Tok 1 ] ~uses:[ Tok 1; UP up ] ~late:[ UR a; UR (a + 1); UR bb; UR (bb + 1); UR d; UR e; UR idesc ]
               ~lat:(Fixed 12) ~min_stall:12
               (pf "UTCHMMA gdesc[UR%d], gdesc[UR%d], tmem[UR%d], tmem[UR%d], idesc[UR%d], UP%d" a bb d e idesc up)))

let ldtm_off b d ~n ~addr ~imm =
  let a = if imm = 0 then pf "tmem[UR%d]" addr else pf "tmem[UR%d+%s]" addr (hex imm) in
  push b (I (mk ~defs:(regs d n) ~uses:[ UR addr ] ~lat:Variable ~pipe:"lsu" (pf "LDTM.x%d R%d, %s" n d a)))

let utmacctl_pf b ~map = push b (I (mk ~late:(urs map 2) ~lat:Variable (pf "UTMACCTL.PF [UR%d]" map)))
let ur_lea_r b d a u sh = lea_ur b d a u sh

let utchmma_acc b ~a ~bb ~d ~e ~idesc ~acc =
  push b (I (mk ~defs:[ Tok 1 ] ~uses:[ Tok 1 ] ~late:[ UR a; UR (a + 1); UR bb; UR (bb + 1); UR d; UR e; UR idesc ]
               ~lat:(Fixed 12) ~min_stall:12
               (pf "UTCHMMA gdesc[UR%d], gdesc[UR%d], tmem[UR%d], tmem[UR%d], idesc[UR%d], %s" a bb d e idesc (if acc then "UPT" else "!UPT"))))

(* the lowest active lane, for the code that must run once per warp *)
let elect b p = push b (I (mk ~defs:[ P p ] ~lat:(Fixed 13) (pf "ELECT P%d, URZ, PT" p)))

let ulop3_xor_imm b d a imm =
  push b (I (mk ~defs:[ UR d ] ~uses:[ UR a ] ~lat:alu (pf "ULOP3.LUT UR%d, UR%d, %s, URZ, 0x3c, !UPT" d a (hex imm))))

(* the tensor core signals this barrier in every CTA the mask selects *)
let utcbar_mc b ~mbar ~mask =
  push b (I (mk ~defs:[ Tok 1 ] ~uses:[ Tok 1 ] ~late:[ UR mbar; UR mask ] ~lat:(Fixed 12) ~min_stall:12
               (pf "UTCBAR.MULTICAST [UR%d], URZ, UR%d" mbar mask)))

(* the two-CTA form: one instruction covers the accumulator of a CTA pair, so
   only the leader issues it and it is guarded on the leader predicate *)
let utchmma2 b ~guard ~a ~bb ~d ~e ~idesc ~acc =
  push b (I (mk ~guard:(pf "@UP%d " guard) ~defs:[ Tok 1 ] ~uses:[ Tok 1; UP guard ]
               ~late:[ UR a; UR (a + 1); UR bb; UR (bb + 1); UR d; UR e; UR idesc ] ~lat:(Fixed 12) ~min_stall:12
               (pf "UTCHMMA.2CTA gdesc[UR%d], gdesc[UR%d], tmem[UR%d], tmem[UR%d], idesc[UR%d], %s"
                  a bb d e idesc (if acc then "UPT" else "!UPT"))))

let utchmma2_up b ~guard ~a ~bb ~d ~e ~idesc ~up =
  push b (I (mk ~guard:(pf "@UP%d " guard) ~defs:[ Tok 1 ] ~uses:[ Tok 1; UP guard; UP up ]
               ~late:[ UR a; UR (a + 1); UR bb; UR (bb + 1); UR d; UR e; UR idesc ] ~lat:(Fixed 12) ~min_stall:12
               (pf "UTCHMMA.2CTA gdesc[UR%d], gdesc[UR%d], tmem[UR%d], tmem[UR%d], idesc[UR%d], UP%d"
                  a bb d e idesc up)))

let utcbar2_mc b ~guard ~mbar ~mask =
  push b (I (mk ~guard:(pf "@UP%d " guard) ~defs:[ Tok 1 ] ~uses:[ Tok 1; UP guard ] ~late:[ UR mbar; UR mask ]
               ~lat:(Fixed 12) ~min_stall:12
               (pf "UTCBAR.2CTA.MULTICAST [UR%d], URZ, UR%d" mbar mask)))

let uisetp_eq0 b up a =
  push b (I (mk ~defs:[ UP up ] ~uses:[ UR a ] ~lat:(Fixed 13) (pf "UISETP.EQ.U32.AND UP%d, UPT, UR%d, URZ, UPT" up a)))

(* shared-memory staging for the epilogue: a warp writes its rows, then reads
   them back so that consecutive lanes hold consecutive addresses *)
let sts_r b ~width ~r ~imm ~data =
  let n = width / 32 in
  let suffix = if width = 32 then "" else pf ".%d" width in
  push b (I (mk ~late:(R r :: regs data n) ~lat:Variable ~pipe:"lsu"
               (pf "STS%s [R%d+%s], R%d" suffix r (hex imm) data)))

let lds_r b ~width d ~r ~imm =
  let n = width / 32 in
  let suffix = if width = 32 then "" else pf ".%d" width in
  push b (I (mk ~defs:(regs d n) ~uses:[ R r ] ~lat:Variable ~pipe:"lsu"
               (pf "LDS%s R%d, [R%d+%s]" suffix d r (hex imm))))

let warpsync b = push b (I (mk ~defs:[ Tok 0 ] ~uses:[ Tok 0 ] ~lat:(Fixed 6) ~min_stall:5 "WARPSYNC.ALL"))

let mov_rr b d a = push b (I (mk ~defs:[ R d ] ~uses:[ R a ] ~lat:alu (pf "IMAD.MOV.U32 R%d, RZ, RZ, R%d" d a)))

(* UTMASTG.2D [URg], [URmap]: URg = shared source, URg+1 = x, URg+2 = y. The
   copy engine writes global memory, so a warp issues one instruction for its
   whole block instead of a store per row. *)
let utmastg b ~g ~map =
  push b (I (mk ~late:(urs g 4 @ urs map 2) ~lat:Variable ~min_stall:2
               (pf "UTMASTG.2D [UR%d], [UR%d]" g map)))

(* the form carries no write scoreboard, so it is ordered by the token alone *)
(* the flush carries the scoreboard the following wait names: ptxas emits it
   with readbar=0 and then DEPBAR.LE SB0, 0x0 *)
let utmacmdflush b =
  push b (I (mk ~defs:[ Tok 0 ] ~uses:[ Tok 0 ] ~late:[ Tok 3 ] ~lat:(Fixed 6) ~force_rb:0 "UTMACMDFLUSH"))

(* wait for the copy engine to have taken the staged block before it is reused *)
let depbar_drain b = push b (I (mk ~defs:[ Tok 0 ] ~uses:[ Tok 0 ] ~lat:(Fixed 6) ~min_stall:4 "DEPBAR.LE SB0, 0x0"))

let lop3_xor_imm_r b d a imm =
  push b (I (mk ~defs:[ R d ] ~uses:[ R a ] ~lat:alu (pf "LOP3.LUT R%d, R%d, %s, RZ, 0x3c, !PT" d a (hex imm))))
