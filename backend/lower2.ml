(* Lowering of the second DSL: TMA into a ring of swizzled shared-memory
   stages, tcgen05 MMA out of them into tensor memory, mbarrier pipes
   between the roles, a tensor-map store of the accumulator.

   Every address, offset, descriptor field and tensor-map box below is read
   off a layout. The instruction that consumes a tile fixes the tile's layout
   (Atom); a copy is compiled from the layouts of its two ends by composing
   the moving instruction's fragment with the storage it reads or writes;
   the composite's strided form, or its pipeline, is what Emit turns into
   instructions. Nothing here writes a lane's address by hand. *)

open Layouts
open Dsl2

let round_up a m = (a + m - 1) / m * m
let pow2 n = n > 0 && n land (n - 1) = 0

let rec log2 n = if n <= 1 then 0 else 1 + log2 (n / 2)
let rec gcd a b = if b = 0 then a else gcd b (a mod b)
let lcm a b = a / gcd a b * b
let elem_bytes = Atom.elt_bytes

(* registers *)
let r_tid = 0 and r_warp = 2 and r_lane = 3 and r_tmp = 4 and r_cnt = 8 and r_tmp2 = 9
let r_tilen = 12 and r_tilem = 13 and r_tile = 14 and r_stage = 144 and r_swz = 216

(* registers an emission site may use for its intermediate values; dead once
   the site's results have been read *)
let scratch = List.init 64 (fun i -> 152 + i)
let r_parity = [| 5; 6; 7; 15 |] (* one parity register per pipe, by declaration order *)
let r_data = [| 16; 80 |] (* two 64-register epilogue buffers *)
let p_role = 1 and p_lane0 = 2 and p_loop = 3 and p_lead = 4
(* A stage asks about the next stage once its own work is out, and the
   answer is read when that stage comes: the try-wait's predicate is
   scoreboarded, so the next stage's bookkeeping goes out meanwhile. nvjet's
   producer asks so, after its loads and their expect-tx arrival; asked any
   earlier, the try-wait holds up the arrival behind it in the barrier unit
   (measured: 1536^3 9664 ns against 7520). *)
let p_probe = 6 and r_probe = 145

(* where each role asks: right after its wait, after its stage's work, or not
   at all -- a switch for measuring *)
type probe_at = Probe_off | Probe_early | Probe_late
let probe_mma : probe_at option ref = ref None (* the kernel's [ask_ahead], unless set *)
let probe_prod = ref Probe_off
(* cluster launch control: the parity of the answer ring's barriers, and an
   answer's validity word *)
let r_clc = 10 and r_clc_free = 8 and r_resp = 11
let up_first = 4 (* the cluster's first CTA, where the scheduler runs *)
let ur_clc = 15 (* the address of an answer, or of a barrier in another CTA, where it is used *)

(* uniform registers *)
let ur_desc = 4 and ur_param i = 8 + (2 * i)
let ur_cta = 14 and ur_tmp = 15 and ur_smem = 16 and ur_tile_n = 18 and ur_tile_m = 19
let ur_init = 20 and ur_mma_count = 22 and ur_acc = 24
let ur_mask = 6 (* the cluster's CTA mask, for multicast loads *)
(* A two-dimensional cluster gives each operand its own group. The CTAs that
   split one MMA's rows sit next to each other (rank x), the pairs that work on
   different columns of the same rows sit a pair apart (rank y). So the row
   operand is shared down the y axis and the column operand across the x axis,
   and each has its own mask and its own CTA that issues the load. *)
let ur_mask_a = 34 and ur_mask_b = 35 and ur_mask_b_plain = 42 and ur_rank_y = 43 and ur_rank_x = 21 and ur_peer = 2 and ur_peer_bar = 3 and ur_lead = 1
(* Two masks, and they are encoded differently: a multicast load takes the CTA
   mask in the upper half of its register (0x30000 for a cluster of two), the
   tensor-core commit takes it plain (0x3). Both read from ptxas. *)
let ur_mask_plain = 7
let up_leader = 1 (* the even rank of a pair: the CTA that issues a two-CTA MMA *)
let up_issue_a = 2 (* one CTA per row group loads the rows and multicasts them *)
let up_issue_b = 3
let ur_da = 36 and ur_db = 38 and ur_zero = 40 and ur_idesc = 41
let ur_tma = [| 44; 48 |] and ur_epi = 25
let ur_st = 44 (* the store group, only live in the epilogue *)
let ur_esrc = 23 (* this warp's copy of the staging tile *)
let ur_ey = 0 (* the row coordinate of this warp's blocks *)
let ur_ex = 17 (* and the column coordinate *)
let ur_acc_rep = 17 (* the tensor-core warp's: a stacked block's accumulator address *)
let mma_reverse = ref false (* issue a stacked MMA's blocks last first -- for bisection *)
let mma_by_step = ref false (* interleave a stacked MMA's blocks at every k step -- for measuring *)

(* Scratch for the two operand descriptor bases of the stage being issued.
   Keeping one per stage would cost a register per stage and the pipeline needs
   those for its barriers; the instruction budget is not the constraint. *)
(* Descriptor bases, one pair per ring stage, live in the registers the
   producer uses for its transfer groups: uniform registers are per warp and
   these two roles are different warps, so the ranges cannot collide. Rings
   deeper than this rebuild the base at each stage instead. *)
let ur_dbase_block = 44
let ur_dbase = 34 (* scratch, for the rebuild path *)

type st =
  { b : Sass.t
  ; k : kernel
  ; pipe_slot : (string, int) Hashtbl.t (* first mbarrier slot of a pipe *)
  ; pipe_index : (string, int) Hashtbl.t
  ; smem_dyn : (string, int) Hashtbl.t (* window offset of stage 0 of a tile *)
  ; stage_bytes : int
  ; slot_off : int (* the TMEM address slot, window offset *)
  ; smem_base : int (* the register holding the shared-memory base *)
  ; epi_off : int (* window offset of the epilogue staging area *)
  ; layouts : (string, (Space.logical, Space.physical) Layout.t) Hashtbl.t (* each shared tile's *)
  ; copy_bytes : (string, int) Hashtbl.t (* the space one copy of a shared tile takes *)
  ; mutable labels : int
  ; mutable max_reg : int
  ; mutable mma_seen : int (* MMAs emitted in the current loop body *)
  ; mutable ring_start : int (* the stage the k loop of the tile being emitted starts on *)
  ; mutable desc_of : int option (* the stage whose descriptor bases the rebuild registers hold *)
  ; mutable probe_in : bool (* the stage being emitted has its wait's answer in [p_probe] *)
  ; mutable probe_next : (int * bool) option (* the stage to ask about next, and whether the ring wraps first *)
  ; clc_full : int (* first barrier slot of the answer ring's "answered" barriers *)
  ; clc_empty : int (* and of its "read" barriers *)
  ; clc_resp : int (* window offset of the answers, 16 bytes each *)
  }

let new_label st p = st.labels <- st.labels + 1; Printf.sprintf "%s_%d" p st.labels

(* The CTAs one MMA spans, from the instruction the kernel issues. Over a CTA
   pair the leader issues it and each CTA holds the rows of each operand the
   atom gives it. *)
let mma_ctas (k : kernel) = match Dsl2.mma_atom k with Some u -> u.Atom.ctas | None -> 1

let two_cta st =
  let c = mma_ctas st.k in
  if c > 1 && st.k.cluster <> c then failwith "an MMA over a CTA pair needs a cluster of that pair along M";
  c = 2

let the_atom (k : kernel) =
  match Dsl2.mma_atom k with Some u -> u | None -> failwith "the kernel issues no MMA"

(* the MMA that reads a shared tile, and as which operand *)
let mma_reading (k : kernel) name =
  let rec walk acc = function
    | Mma { atom; a; b; _ } ->
      (if a = name then [ atom, `A ] else []) @ (if b = name then [ atom, `B ] else []) @ acc
    | Kloop body | Role (_, body) -> List.fold_left walk acc body
    | _ -> acc
  in
  match List.sort_uniq compare (List.fold_left walk [] k.body) with
  | [] -> None
  | [ x ] -> Some x
  | _ -> failwith (name ^ ": read by more than one MMA operand")

(* the blocks the MMA reading [name] stacks along its rows: its accumulator's *)
let mma_reps (k : kernel) name =
  let rec walk acc = function
    | Mma { d; a; b; _ } when a = name || b = name -> d :: acc
    | Kloop body | Role (_, body) -> List.fold_left walk acc body
    | _ -> acc
  in
  match List.sort_uniq compare (List.fold_left walk [] k.body) with
  | [ d ] -> (List.find (fun (t : ttile) -> t.tname = d) k.tmem).reps
  | _ -> 1

(* the rows of an operand, or of the result, the atom gives CTA [v] *)
let share_rows (u : Atom.umma) which ~v =
  match which with
  | `A -> Atom.cta_rows (Atom.umma_a u) ~cols:(Atom.umma_k u) ~v
  | `B -> Atom.cta_rows (Atom.umma_b u) ~cols:(Atom.umma_k u) ~v
  | `C -> Atom.cta_rows (Atom.umma_c u) ~cols:u.n ~v

(* the cluster as a rectangle: [cluster] CTAs split an MMA's rows, [cluster_n]
   such pairs work on neighbouring columns of those same rows *)
let ctas (k : kernel) = k.cluster * k.cluster_n
let grid_cluster (k : kernel) = ctas k > 1
let pipe st name = List.find (fun (p : pipe) -> p.pname = name) st.k.pipes
let stile st name = List.find (fun (s : stile) -> s.sname = name) st.k.smem
let gmat st name = List.find (fun (g : gmat) -> g.name = name) st.k.params
let param_index st name = let rec go i = function [] -> failwith name | (g : gmat) :: r -> if g.name = name then i else go (i + 1) r in go 0 st.k.params
(* Every barrier gets a uniform register holding its address. The encoding has
   an offset field on the SYNCS forms and cupatch will assemble one, but ptxas
   never emits it and the hardware does not honour it: with offsets the
   barriers all alias to the base and the handshake deadlocks. *)
let mbar_off_raw st p ~stage ~buf =
  let pp = pipe st p in
  8 * (Hashtbl.find st.pipe_slot p + (if pp.per_stage then stage else if pp.per_buffer then buf else 0))

let mbar_slot st p ~stage ~buf =
  let pp = pipe st p in
  Hashtbl.find st.pipe_slot p + (if pp.per_stage then stage else if pp.per_buffer then buf else 0)

(* UR26-33 and UR52-62: UR63 is URZ *)
let mbar_reg_of_slot slot =
  if slot < 8 then 26 + slot else if slot < 19 then 52 + (slot - 8) else failwith "out of barrier registers"

let mbar_reg st p ~stage ~buf =
  let slot = mbar_slot st p ~stage ~buf in
  mbar_reg_of_slot slot

(* A barrier's address as a uniform register and an immediate: the first 19
   slots each have a register, the rest are the last register plus 8 bytes a
   slot -- the [UR+imm] form ptxas uses, the immediate recorded in the
   driver's barrier table (sasm.py). UR63 is URZ, which is why there are 19. *)
let bar_regs = 19

let mbar_addr_of_slot slot =
  if slot < bar_regs then mbar_reg_of_slot slot, 0 else mbar_reg_of_slot (bar_regs - 1), 8 * (slot - (bar_regs - 1))

let mbar_addr st p ~stage ~buf = mbar_addr_of_slot (mbar_slot st p ~stage ~buf)
(* the bytes a layout's image spans: through the last byte of the element at
   its largest offset *)
let footprint l ~elem = elem + List.fold_left (fun m c -> max m (Layout.offset l c)) 0 (Coord.enumerate (Layout.shape l))

(* The layout of a shared tile is fixed by the instruction that reads it: an
   MMA operand is the K-major SWIZZLE_128B image its descriptor describes, a
   store's staging tile the SWIZZLE_128B box the copy engine reads. The other
   access to the tile -- the load that fills an operand, the warps that write
   the staging tile -- is compiled against that layout and checked there. *)
let rec reads pred body = List.exists (function Kloop b | Role (_, b) -> reads pred b | s -> pred s) body

let tile_layout (k : kernel) (t : stile) =
  let elem = elem_bytes t.sdtype in
  let l = Atom.swizzled_rows ~rows:t.srows ~cols:t.scols ~elem in
  let by_mma = mma_reading k t.sname in
  let by_store = reads (function Store { via; _ } -> via = t.sname | _ -> false) k.body in
  let filled = reads (function Tma { dst; _ } -> dst = t.sname | _ -> false) k.body in
  (match by_mma, by_store with
   | Some (u, which), false ->
     (* the atom says where the operand is read from, its major, and the rows
        of it each CTA holds *)
     (match which, u.a_src with
      | `A, Atom.Tmem -> failwith (t.sname ^ ": the MMA reads A from tensor memory, not from this tile")
      | _ -> ());
     if (match which with `A -> u.a_major | `B -> u.b_major) <> Atom.K_major
     then failwith (t.sname ^ ": only K-major operands are lowered");
     if t.sdtype <> u.ab then failwith (t.sname ^ ": the tile's type is not the MMA's operand type");
     (* A holds the rows of every block the MMA stacks, block after block *)
     let rows = snd (share_rows u (which :> [ `A | `B | `C ]) ~v:0) * (match which with `A -> mma_reps k t.sname | `B -> 1) in
     if t.srows <> rows then failwith (Printf.sprintf "%s: the atom gives each CTA %d rows, the tile has %d" t.sname rows t.srows);
     ignore (Atom.umma_kmajor l ~elem ~mma_k:(Atom.umma_k u))
   | None, true -> ignore (Atom.tma_box l ~elem)
   | None, false -> failwith (t.sname ^ ": no instruction reads this tile, so nothing fixes its layout")
   | Some _, true -> failwith (t.sname ^ ": read both by an MMA and by a store"));
  if filled then ignore (Atom.tma_box l ~elem);
  l

(* the MMA descriptor of an operand tile placed at window offset [off]: the
   start address in the low word with the fixed leading-offset field, SBO and
   the layout type in the high word, all read off the tile's layout *)
let desc_low st ~ur ~off =
  let b = st.b in
  Sass.uiadd3 b ur ur_smem off;
  Sass.ushf_r b ur ur 4;
  Sass.ulop3_and b ur ur 0x3fff;
  Sass.ulop3_or b ur ur Atom.desc_low_fixed

let operand_desc st name =
  let t = stile st name in
  Atom.umma_kmajor (Hashtbl.find st.layouts name) ~elem:(elem_bytes t.sdtype) ~mma_k:(Atom.umma_k (the_atom st.k))

(* A debugging build: every pipe wait gives up after [debug_spins] tries,
   writes which wait it was to the debug buffer (the kernel's last parameter,
   8 bytes per CTA and warp: the wait's number and its parity), and leaves.
   The header lists what each number is. *)
let debug_waits = ref false
let debug_spins = 4_000_000
let debug_sites : string list ref = ref []

(* A timing build: where a warp passes a phase boundary it writes the global
   timer's low word to the stamp buffer (the kernel's last parameter), 16
   words a CTA, one per event. Program order is kept, so the stamp is where
   it is emitted. *)
let stamps = ref false
let r_stamp = 248 (* 248: the time, 250-251: the word's address, 252: the CTA, 253: the role's tile count *)
let stamp_names =
  [ 0, "entry"; 1, "barriers initialised, cluster met"; 2, "producer starts"; 3, "producer done"; 4, "MMA warp starts"
  ; 5, "MMA warp done"; 6, "epilogue starts"; 7, "epilogue: accumulator ready"; 8, "epilogue done"
  ; 9, "MMA: first stage landed"; 10, "epilogue leaves"; 12, "producer: tile issued"; 13, "MMA: tile issued"
  ; 14, "epilogue: tile stored" ]

(* 64 words a CTA: the events of its first four tiles, 16 each, a tile's
   events at 16 x (the role's tile count mod 4) *)
let stamp st ev =
  if !stamps then begin
    let b = st.b in
    Sass.s2r_timer b r_stamp;
    Sass.ldc64 b (r_stamp + 2) (0x380 + (8 * List.length st.k.params));
    Sass.s2r_ctaid b (r_stamp + 4) ~axis:"X";
    Sass.imad_wide b (r_stamp + 2) (r_stamp + 4) 256 (r_stamp + 2);
    Sass.lop3_and b (r_stamp + 1) (r_stamp + 5) 3;
    Sass.imad_wide b (r_stamp + 2) (r_stamp + 1) 64 (r_stamp + 2);
    Sass.stg32 b ~base:(r_stamp + 2) ~imm:(4 * ev) ~data:r_stamp;
    st.max_reg <- max st.max_reg (r_stamp + 5)
  end

(* A timing build of the stages: the MMA warp writes the global timer each
   time a stage has landed, 4096 words a CTA, a running count mod 4096 *)
let stage_stamps = ref false
let r_stage_n = 246

let stamp_stage st =
  if !stage_stamps then begin
    let b = st.b in
    Sass.s2r_timer b r_stamp;
    Sass.ldc64 b (r_stamp + 2) (0x380 + (8 * List.length st.k.params));
    Sass.s2r_ctaid b (r_stamp + 4) ~axis:"X";
    Sass.imad_wide b (r_stamp + 2) (r_stamp + 4) (4 * 4096) (r_stamp + 2);
    Sass.lop3_and b (r_stamp + 1) r_stage_n 4095;
    Sass.imad_wide b (r_stamp + 2) (r_stamp + 1) 4 (r_stamp + 2);
    Sass.stg32 b ~base:(r_stamp + 2) ~imm:0 ~data:r_stamp;
    Sass.iadd3_c b r_stage_n r_stage_n 1;
    st.max_reg <- max st.max_reg r_stage_n
  end

let stamp_count_reset st = if !stamps then Sass.mov_imm st.b (r_stamp + 5) 0
let stamp_count_next st = if !stamps then Sass.iadd3_c st.b (r_stamp + 5) (r_stamp + 5) 1

let lower_wait st p ~stage ~buf =
  let pp = pipe st p in
  let r = r_parity.(Hashtbl.find st.pipe_index p) in
  let l = new_label st "WAIT" in
  let base, imm = mbar_addr st p ~stage ~buf in
  if !debug_waits
  then begin
    let id = List.length !debug_sites + 1 in
    debug_sites := Printf.sprintf "wait %d: %s stage %d buf %d ring_start %d" id p stage buf st.ring_start :: !debug_sites;
    let passed = new_label st "WAITED" and give_up = new_label st "GIVE_UP" in
    Sass.mov_imm st.b r_resp 0;
    Sass.label st.b l;
    Sass.syncs_trywait st.b 0 ~base ~imm ~parity_reg:(Some r);
    Sass.bra st.b 0 passed;
    Sass.iadd3_c st.b r_resp r_resp 1;
    Sass.isetp_lt_u32_imm st.b 5 r_resp debug_spins;
    Sass.bra st.b 5 l;
    Sass.jmp st.b give_up;
    Sass.label st.b give_up;
    (* out[ctaid * 8 + warp] = (id, parity) *)
    Sass.ldc64 st.b 20 (0x380 + (8 * List.length st.k.params));
    Sass.s2r_ctaid st.b 22 ~axis:"X";
    Sass.imad st.b 22 22 8 r_warp;
    Sass.imad_wide st.b 20 22 8 20;
    Sass.mov_imm st.b 24 id;
    Sass.mov_rr st.b 25 r;
    Sass.stg64 st.b ~base:20 ~imm:0 ~data:24;
    Sass.exit st.b;
    Sass.label st.b passed
  end
  else begin
    (* a warp that finds the barrier not yet complete sleeps before asking
       again: spinning on it without a pause hangs the two-CTA kernel at ring
       depth 7 in most launches (measured, 11 of 12), as if the waiters kept
       the barrier unit from the arrivals they wait for *)
    Sass.label st.b l;
    Sass.syncs_trywait st.b 0 ~base ~imm ~parity_reg:(Some r);
    Sass.nanosleep_syncs st.b ~neg:true 0;
    Sass.bra st.b ~neg:true 0 l
  end;

  (* a barrier used once per tile completes a phase here; one used once per
     stage completes it when the k loop comes round, and flips there *)
  (* Barriers that belong to a group -- one per ring stage, one per accumulator
     buffer -- all advance one phase per pass over the group, so their shared
     parity flips once per pass, where the pass ends. A barrier used once per
     tile completes its phase right here. *)
  if (not pp.per_stage) && not pp.per_buffer then Sass.lop3_xor_imm st.b r r 0x80000000

(* The pair shares one accumulator: the tensor core wrote half of it into each
   CTA, so the leader may not start the next tile until the partner's epilogue
   has read its half out too.  A local arrival cannot say that, so the release
   is repeated on the partner's copy of the barrier.  Arriving on a peer
   barrier is legal; waiting on one is not. *)
let tma_pipe_of (k : kernel) name =
  let rec walk = function
    | Tma { pipe; _ } -> pipe = name
    | Kloop body | Role (_, body) -> List.exists walk body
    | _ -> false
  in
  List.exists walk k.body

let ttile st name = List.find (fun (t : ttile) -> t.tname = name) st.k.tmem

(* An accumulator's tensor-memory layout is the one the atom that writes it
   fixes, and so are the columns one block of it spans; a probe that runs
   no MMA has the 128-lane layout. *)
let acc_image (k : kernel) (acc : ttile) =
  match Dsl2.mma_atom k with Some u -> Atom.tmem_acc u | None -> Atom.tmem_accumulator ~rows:acc.trows ~cols:acc.tcols

let acc_span (k : kernel) (acc : ttile) = match Dsl2.mma_atom k with Some u -> Atom.tmem_acc_columns u | None -> acc.tcols

(* the hardware coordinates a fragment's thread coordinates stand for *)
let hw_reg = function "warpid" -> r_warp | "laneid" -> r_lane | v -> failwith ("unbound coordinate " ^ v)
let hw_range st = function "warpid" -> st.k.nwarps | "laneid" -> 32 | v -> failwith ("unbound coordinate " ^ v)

(* A value over runtime coordinates [rt] and a compile-time index 0 .. n-1,
   emitted as one expression in the runtime coordinates plus an immediate per
   index. The expression is the strided form of the map at index 0, decided;
   each immediate is read off by evaluation, and the split is refused unless
   the index shifts the value by the same amount at every runtime point. *)
let split ~name ~rt ~n f =
  let pts = Coord.enumerate rt in
  let e =
    match Decide.strided_form ~shape:rt ~offset:(fun c -> f c 0) with
    | Some e -> e
    | None -> failwith (name ^ ": no strided form over the runtime coordinates")
  in
  let imm k =
    match List.sort_uniq compare (List.map (fun c -> f c k - f c 0) pts) with
    | [ d ] -> d
    | _ -> failwith (name ^ ": the compile-time index does not shift the value by a constant")
  in
  e, Array.init n imm

(* In a pair only the leader waits on the barrier -- its tensor-core warp
   issues the pair's MMAs -- so both CTAs arrive on the leader's copy, as
   nvjet's epilogues do (the CTA field with the pair bit cleared). The other
   copy then receives nothing, and the leader, which waits for the last
   release before it leaves, is the only CTA a release is still in flight
   towards. *)
let release_to_pair st p ~stage ~buf =
  if two_cta st && not (pipe st p).cross
  then begin
    Sass.uiadd3 st.b ur_peer_bar ur_lead (8 * mbar_slot st p ~stage ~buf);
    Sass.syncs_arrive_red st.b ~guard:p_lane0 ~base:ur_peer_bar ~imm:0
  end
  else
    let base, imm = mbar_addr st p ~stage ~buf in
    Sass.syncs_arrive st.b ~guard:p_lane0 ~base ~imm

(* The output coordinate an accumulator's rows -- its tensor-memory lanes --
   stand for: the rows of the MMA's A operand, whichever matrix the load that
   fills that operand reads. An accumulator no MMA writes (a probe) is taken
   in the output's own orientation. *)
let acc_rows_coord (k : kernel) acc =
  let rec mma = function
    | Mma { d; a; _ } when d = acc -> [ a ]
    | Kloop b | Role (_, b) -> List.concat_map mma b
    | _ -> []
  in
  match List.sort_uniq compare (List.concat_map mma k.body) with
  | [] -> Tile_m
  | [ a ] ->
    let rec fill = function
      | Tma { dst; rows; _ } when dst = a -> [ rows ]
      | Kloop b | Role (_, b) -> List.concat_map fill b
      | _ -> []
    in
    (match List.sort_uniq compare (List.concat_map fill k.body) with
     | [ r ] -> r
     | _ -> failwith (a ^ ": filled from no matrix, or from several"))
  | _ -> failwith (acc ^ ": written by MMAs with different operands")

(* [rows] x [cols] indices, read as the index of the transposed [cols] x
   [rows]: (i, j) -> j * rows + i *)
let transpose ~rows ~cols : (Space.logical, Space.logical) Layout.t =
  Layout.of_linear (Group [ Axis { size = rows; stride = 1 }; Axis { size = cols; stride = rows } ])

(* Everything a store needs, derived and checked, with nothing emitted: the
   layouts it composes, the expressions it will emit, the immediates. The
   runtime coordinate of every expression is the warp's lane quarter, "c";
   the compile-time index is the block along the load's chunks. *)
type store_plan =
  { sp_dst : string
  ; e_ld : Expr.t
  ; imm_ld : int array
  ; e_copy : Expr.t
  ; e_y : Expr.t
  ; imm_y : int array
  ; e_x : Expr.t
  ; imm_x : int array
  ; sts : (Space.thread_value, Space.physical) Layout.t
  ; sp_n : int (* registers per lane per load *)
  ; vec : int (* elements per shared-memory store *)
  ; sp_elem : int
  ; copy : int
  ; copies : int
  ; blocks_ch : int
  ; rep_ld : int array (* per stacked block: its tensor-memory offset *)
  ; rep_y : int array (* and its offset in the output tile *)
  ; rep_x : int array
  }

let store_plan st ~dst ~src ~via =
  let acc = ttile st src and sc = stile st via in
  let box = Hashtbl.find st.layouts via in
  let copies =
    match sc.ring with Per_warp n -> n | Stages -> failwith (via ^ ": a staging tile has copies per warp")
  in
  let copy = Hashtbl.find st.copy_bytes via in
  let elem = elem_bytes sc.sdtype in
  let lanes = Atom.ldtm_block in
  (* The accumulator's lanes are output rows, or -- when the MMA's A operand
     is the second matrix -- output columns: then the CTA's output tile is the
     accumulator transposed. *)
  let lanes_are_cols = acc_rows_coord st.k src = Tile_n in
  let out_cols = if lanes_are_cols then acc.trows else acc.tcols in
  (* the map from the accumulator's coordinates to the output tile's index *)
  let to_out ~rows ~cols = if lanes_are_cols then transpose ~rows ~cols else Layout.of_linear (Linear.canonical (Product [ Bound rows; Bound cols ])) in
  (* One tcgen05.ld.32x32b covers 32 lanes by n columns of the accumulator:
     in output coordinates, the staging tile. *)
  let n = if lanes_are_cols then sc.srows else sc.scols in
  if (if lanes_are_cols then sc.scols else sc.srows) <> lanes
  then failwith (via ^ ": the staging tile spans the 32 lanes of a warp's quarter");
  let frag = Atom.ldtm_32x32b ~n in
  let block = Shape.Product [ Bound lanes; Bound n ] in
  let blocks_w = acc.trows / lanes and blocks_ch = acc.tcols / n in
  (* The load's fragment, dealt over the accumulator's blocks and composed
     with the accumulator's layout, is the load's address map; Atom checks it
     against what one warp-uniform address reads. The blocks divide the
     accumulator's row-major index, which the atom's layout then decodes. *)
  let blocked = Layout.divide ~by:block (Layout.of_linear (Linear.canonical (Product [ Bound acc.trows; Bound acc.tcols ]))) in
  let ld =
    Layout.compose
      (Layout.interleave ~by:(Linear.canonical (Product [ Bound blocks_w; Bound blocks_ch ])) frag)
      (Layout.compose blocked (acc_image st.k acc))
  in
  let at w ch l r = Layout.offset ld (Coord.Tuple [ Tuple [ Idx w; Idx ch ]; Tuple [ Idx l; Idx r ] ]) in
  Atom.check_ldtm ~at ~blocks_w ~blocks_ch ~n;
  (* Each block is loaded by the warp of its lane quarter, in the order of
     its place along the accumulator; every quarter gets as many. *)
  let quarters = 4 in
  let of_quarter =
    Array.init quarters (fun q ->
      List.concat_map
        (fun w -> List.filter_map (fun ch -> if Atom.ldtm_quarter ~at w ch = q then Some (w, ch) else None) (List.init blocks_ch Fun.id))
        (List.init blocks_w Fun.id))
  in
  let per_warp = List.length of_quarter.(0) in
  if Array.exists (fun l -> List.length l <> per_warp) of_quarter || per_warp * quarters <> blocks_w * blocks_ch
  then failwith (src ^ ": the accumulator's blocks are not spread evenly over the four lane quarters");
  let block_of q j = List.nth of_quarter.(q) j in
  let rt = Shape.Bound quarters in
  let w_of = function Coord.Idx w -> w | Tuple _ -> assert false in
  let at_block c j = let w, ch = block_of (w_of c) j in at w ch 0 0 in
  let e_ld, imm_ld = split ~name:"tensor-memory load" ~rt ~n:per_warp (fun c j -> at_block c j) in
  (* The staging write is the same fragment, taken to output coordinates and
     composed with the staging tile's layout -- the box the copy engine reads
     -- so a register's address is where the store will look for it. *)
  let sts = Layout.compose frag (Layout.compose (to_out ~rows:lanes ~cols:n) box) in
  if not (Layout.is_injective sts) then failwith (via ^ ": two values of a fragment land on one address");
  (* the widest store whose registers are contiguous and aligned, read off the
     composite: 16 bytes when a lane's registers run along a staging row, one
     element when they run down its columns *)
  let reg_addr l r = Layout.offset sts (Coord.Tuple [ Idx l; Idx r ]) in
  let fits v =
    n mod v = 0
    && List.for_all
         (fun l ->
           List.for_all
             (fun q ->
               let a0 = reg_addr l (v * q) in
               a0 mod (v * elem) = 0 && List.for_all (fun e -> reg_addr l ((v * q) + e) = a0 + (e * elem)) (List.init v Fun.id))
             (List.init (n / v) Fun.id))
         (List.init lanes Fun.id)
  in
  let vec = List.find fits (List.filter (fun v -> v >= 1) [ 16 / elem; 8 / elem; 4 / elem; 1 ]) in
  (* A block's place in the output is its place in the accumulator's division
     into blocks, taken to output coordinates; the copy engine takes it as a
     coordinate pair. *)
  let tile : (Space.logical, Space.logical) Layout.t =
    Layout.compose
      (Layout.divide ~by:block (Layout.of_linear (Linear.canonical (Product [ Bound acc.trows; Bound acc.tcols ]))))
      (to_out ~rows:acc.trows ~cols:acc.tcols)
  in
  let origin w ch = Layout.offset tile (Coord.Tuple [ Tuple [ Idx 0; Idx 0 ]; Tuple [ Idx w; Idx ch ] ]) in
  let origin_of c j = let w, ch = block_of (w_of c) j in origin w ch in
  let e_y, imm_y = split ~name:"store row" ~rt ~n:per_warp (fun c j -> origin_of c j / out_cols) in
  let e_x, imm_x = split ~name:"store column" ~rt ~n:per_warp (fun c j -> origin_of c j mod out_cols) in
  (* A stacked MMA's block r is the same accumulator r * tcols columns on,
     and in the output it is the block of rows r * trows of the MMA's rows on:
     where those land is read off the whole accumulator taken to output
     coordinates. *)
  let reps = acc.reps in
  let full_rows = reps * acc.trows in
  let full_out_cols = if lanes_are_cols then full_rows else acc.tcols in
  let rep_origin r = Layout.offset (to_out ~rows:full_rows ~cols:acc.tcols) (Coord.Tuple [ Idx (r * acc.trows); Idx 0 ]) in
  let rep_ld = Array.init reps (fun r -> r * acc_span st.k acc) in
  let rep_y = Array.init reps (fun r -> rep_origin r / full_out_cols) in
  let rep_x = Array.init reps (fun r -> rep_origin r mod full_out_cols) in
  (* the warp's copies of the staging tile *)
  let e_copy = Expr.scale (copies * copy) (Expr.var "c") in
  { sp_dst = dst; e_ld; imm_ld; e_copy; e_y; imm_y; e_x; imm_x; sts; sp_n = n; vec; sp_elem = elem; copy; copies
  ; blocks_ch = per_warp; rep_ld; rep_y; rep_x }

let quarter e = Expr.bind "c" (Expr.modulo (Expr.var "warpid") 4) e

(* Once per kernel, before the tile loop: the addresses that depend only on
   the warp and the lane -- where this warp's staging copies are and where
   each of its lane's vectors goes in them. They are the same for every tile,
   and emitting them here takes them off the path from the accumulator being
   ready to its first store. *)
let store_setup st (p : store_plan) =
  let b = st.b in
  let em = Emit.create b ~scratch in
  let range = hw_range st and reg = hw_reg in
  Emit.into em ~range ~reg (quarter p.e_copy) ~dst:r_stage;
  Sass.lea_ur b r_stage r_stage ur_smem 0;
  Sass.iadd3_c b r_stage r_stage st.epi_off;
  Sass.r2ur b ur_esrc r_stage;
  for q = 0 to (p.sp_n / p.vec) - 1 do
    let e = Restricted.expr (Restricted.restrict ~at:(Parts [ Free; At (p.vec * q) ]) p.sts) in
    Emit.into em ~range ~reg (Expr.bind "c0" (Expr.var "laneid") e) ~dst:(r_swz + q);
    Sass.iadd3 b (r_swz + q) (r_swz + q) r_stage
  done;
  st.max_reg <- max st.max_reg (max em.high (r_swz + (p.sp_n / p.vec) - 1))

(* per tile: the accumulator buffer's load address and the output row, then
   the blocks *)
let store_body st (p : store_plan) ~release ~buf =
  let b = st.b in
  let n = p.sp_n and vec = p.vec and elem = p.sp_elem and copy = p.copy and copies = p.copies in
  let em = Emit.create b ~scratch in
  let range = hw_range st and reg = hw_reg in
  Emit.into em ~range ~reg (quarter p.e_ld) ~dst:r_tmp2;
  Sass.lea_ur b r_tmp2 r_tmp2 ur_acc 0;
  Sass.r2ur b ur_epi r_tmp2;
  (* a block coordinate the warp does not change is the tile's origin plus an
     immediate; one it does is computed once per tile *)
  let coord e ~origin ~into =
    match e with
    | Expr.Const k -> origin, k
    | e ->
      Emit.into em ~range ~reg (quarter e) ~dst:r_tmp;
      Sass.lea_ur b r_tmp r_tmp origin 0;
      Sass.r2ur b into r_tmp;
      into, 0
  in
  let ur_y, y0 = coord p.e_y ~origin:ur_tile_m ~into:ur_ey in
  let ur_x, x0 = coord p.e_x ~origin:ur_tile_n ~into:ur_ex in
  st.max_reg <- max st.max_reg em.high;
  let imm_ld = p.imm_ld and imm_x = p.imm_x and imm_y = p.imm_y and blocks_n = p.blocks_ch in
  let dst = p.sp_dst in
  let reps = Array.length p.rep_ld in
  (* Each block's tensor-memory load goes out as soon as the block before it
     has been staged, into the other register buffer: its latency runs under
     that block's fence and store instead of ahead of this block's writes. *)
  let blocks = List.concat_map (fun r -> List.init blocks_n (fun ch -> r, ch)) (List.init reps Fun.id) in
  let nblk = List.length blocks in
  let load blk =
    let r, ch = List.nth blocks blk in
    let d = r_data.(blk mod 2) in
    Sass.ldtm_off b d ~n ~addr:ur_epi ~imm:(imm_ld.(ch) + p.rep_ld.(r));
    st.max_reg <- max st.max_reg (d + n - 1)
  in
  load 0;
  for r = 0 to reps - 1 do
    for ch = 0 to blocks_n - 1 do
      (* the staging copies and the load registers alternate over every block
         of the tile, stacked blocks included *)
      let blk = (r * blocks_n) + ch in
      let d = r_data.(blk mod 2) and slot = blk mod copies in
      (* The copy this block goes into was last read by the store [copies]
         blocks back -- in this tile or the previous one. Stores finish in
         order, so at most [copies - 1] may still be reading when it is
         rewritten: the rest keep going while this block is staged. *)
      Sass.depbar_le b ~n:(copies - 1);
      for q = 0 to (n / vec) - 1 do
        Sass.sts_r b ~width:(8 * vec * elem) ~r:(r_swz + q) ~imm:(slot * copy) ~data:(d + (vec * q))
      done;
      if blk + 1 < nblk then load (blk + 1);
      (* the stores have taken the last block's values, so the load that
         produced them has landed: the accumulator is free for the next tile's
         MMAs while its last blocks are still being written out *)
      if r = reps - 1 && ch = blocks_n - 1 then (match release with Some p -> release_to_pair st p ~stage:0 ~buf | None -> ());
      (* The copy engine reads the staging copy, so the writes into it must
         have landed, not merely issued: a read scoreboard only says the store
         has taken its data out of the registers. The fence publishes them to
         the async proxy and the wait comes after it -- waiting first leaves
         the youngest stores unpublished and the engine reads the sixteen bytes
         they were about to overwrite. *)
      Sass.fence_view_async b;
      Sass.warpsync b;
      Sass.uiadd3 b ur_st ur_esrc (slot * copy);
      Sass.uiadd3 b (ur_st + 1) ur_x (x0 + imm_x.(ch) + p.rep_x.(r));
      Sass.uiadd3 b (ur_st + 2) ur_y (y0 + imm_y.(ch) + p.rep_y.(r));
      Sass.utmastg b ~g:ur_st ~map:(ur_param (param_index st dst));
      Sass.utmacmdflush b
    done
  done

(* The first row of an operand CTA rank v loads, relative to the tile origin
   its load starts from: the atom's share of the operand, less the share of
   the result that origin already places this CTA at. The CTA-to-tile map
   puts the ranks of a pair on consecutive tiles along the coordinate the
   accumulator's rows stand for, so an origin along that coordinate includes
   the result's share and the other includes none. The offset must be a
   multiple of the rank. *)
let rank_stride st ~dst ~rows =
  match mma_reading st.k dst with
  | None -> 0
  | Some (u, which) ->
    let acc_rows = acc_rows_coord st.k (List.hd st.k.tmem).tname in
    let off v = fst (share_rows u (which :> [ `A | `B | `C ]) ~v) - (if rows = acc_rows then fst (share_rows u `C ~v) else 0) in
    let stride = if u.ctas > 1 then off 1 - off 0 else 0 in
    for v = 0 to u.ctas - 1 do
      if off v <> v * stride then failwith (dst ^ ": the rows a CTA loads are not a multiple of its rank")
    done;
    if off 0 <> 0 then failwith (dst ^ ": rank 0 does not load from the tile origin");
    stride

(* the tensor core's commit names its barrier by a register alone: one past
   the registers is computed into a scratch register first *)
let commit_bar st p ~stage ~buf =
  match mbar_addr st p ~stage ~buf with
  | r, 0 -> r
  | r, imm ->
    Sass.uiadd3 st.b ur_tmp r imm;
    ur_tmp

(* ask whether stage [stage] of a ring's barrier has completed the phase its
   next use waits for: this pass's, or -- past the ring's last stage -- the
   next pass's *)
let probe st p ~stage ~wraps =
  let r = r_parity.(Hashtbl.find st.pipe_index p) in
  let parity = if wraps then (Sass.lop3_xor_imm st.b r_probe r 0x80000000; r_probe) else r in
  st.max_reg <- max st.max_reg r_probe;
  let base, imm = mbar_addr st p ~stage ~buf:stage in
  Sass.syncs_trywait st.b p_probe ~base ~imm ~parity_reg:(Some parity)

let rec lower_stmt st ~stage ~buf ~(tx_done : (string, unit) Hashtbl.t) ~(tma_index : int ref) = function
  | Wait p when (pipe st p).per_stage && not !debug_waits ->
    (* the answer to the question the last stage asked, if it asked: the
       blocking wait runs only when that stage was not yet complete *)
    let ready = new_label st "READY" in
    if st.probe_in then Sass.bra st.b p_probe ready;
    lower_wait st p ~stage ~buf;
    if st.probe_in then Sass.label st.b ready;
    if p = "full" then stamp_stage st;
    (match st.probe_next with Some (next, wraps) -> probe st p ~stage:next ~wraps | None -> ())
  | Wait p ->
    lower_wait st p ~stage ~buf;
    if p = "ready" then stamp st 7
  | Tma { dst; src; rows; pipe = p } ->
    let b = st.b in
    (* A two-CTA MMA reads both CTAs' stages, so the stage is full only when
       both halves have landed. Every load of the pair reports to the LEADER's
       copy of the barrier -- the CTA field of its address with the pair bit
       cleared, as CUTLASS masks it (0xfefffff8) -- and the leader alone states
       the bytes to expect, the pair's whole stage. *)
    let bar_of p = if two_cta st then `Lead (8 * mbar_slot st p ~stage ~buf) else `Own (mbar_addr st p ~stage ~buf) in
    if not (Hashtbl.mem tx_done p) then begin
      Hashtbl.replace tx_done p ();
      if two_cta st
      then begin
        let l = new_label st "NOT_LEADER" in
        Sass.bra b ~neg:true p_lead l;
        (let base, imm = mbar_addr st p ~stage ~buf in
         Sass.syncs_arrive_tx b ~guard:p_lane0 ~base ~imm ~tx:r_tmp2);
        Sass.label b l
      end
      else (let base, imm = mbar_addr st p ~stage ~buf in
            Sass.syncs_arrive_tx b ~guard:p_lane0 ~base ~imm ~tx:r_tmp2)
    end;
    let g = ur_tma.(!tma_index) in
    incr tma_index;
    let base = Hashtbl.find st.smem_dyn dst + (stage * st.stage_bytes) in
    (* In a cluster every operand is needed by more than one CTA: the MMA's A
       rows by the pairs working on neighbouring blocks of the other output
       coordinate, its B rows by the CTAs a one-CTA MMA's cluster splits A
       over. One CTA of each group issues the load and multicasts it, so the
       bytes cross the memory system once per group instead of once per CTA,
       and the copy lands at the same offset in every CTA the mask names. *)
    let operand = match mma_reading st.k dst with Some (_, w) -> w | None -> failwith (dst ^ ": no MMA reads it") in
    ignore rows;
    let group =
      match operand with
      | `A -> st.k.cluster_n
      | `B -> if two_cta st then 1 (* the pair splits B's rows, so nobody shares *) else st.k.cluster
    in
    if grid_cluster st.k && group > 1
    then begin
      let mask, guard = match operand with `A -> (ur_mask_a, up_issue_a) | `B -> (ur_mask_b, up_issue_b) in
      Sass.uiadd3 b g ur_smem base;
      (match bar_of p with
       | `Own (r, imm) -> Sass.uiadd3 b (g + 1) r imm
       | `Lead off -> Sass.uiadd3 b (g + 1) ur_lead off);
      Sass.utmaldg_mc ~guard ~two:(two_cta st) b ~g ~map:(ur_param (param_index st src)) ~mask
    end
    else begin
      Sass.uiadd3 b g ur_smem base;
      (match bar_of p with
       | `Own (r, imm) -> Sass.uiadd3 b (g + 1) r imm
       | `Lead off -> Sass.uiadd3 b (g + 1) ur_lead off);
      Sass.utmaldg ~two:(two_cta st) b ~g ~map:(ur_param (param_index st src))
    end;
    (* the next stage's box starts where this one's K extent ends *)
    Sass.uiadd3 b (g + 2) (g + 2) (snd (Atom.dims (Hashtbl.find st.layouts dst)))
  | Mma { atom; d; a; b = bb } ->
    let b = st.b in
    let da = operand_desc st a and db = operand_desc st bb in
    let acc = ttile st d in
    (* block r of a stacked MMA reads A from row r * (the atom's share) on and
       writes the accumulator r * tcols columns on: both read off the layouts *)
    let a_rows = snd (share_rows atom `A ~v:0) in
    let a_rep r = (Atom.at2 (Hashtbl.find st.layouts a) (r * a_rows) 0 - Atom.at2 (Hashtbl.find st.layouts a) 0 0) / 16 in
    (* one MMA consumes the atom's K columns of the stage; the stage's K extent
       is its layout's *)
    let k_of name = snd (Atom.dims (Hashtbl.find st.layouts name)) in
    if k_of a <> k_of bb then failwith "mma: the operands' stages hold different K extents";
    let steps = k_of a / Atom.umma_k atom in
    (* only the very first MMA of the kernel overwrites the accumulator; that
       one reads a flag the loop body sets, every other one accumulates *)
    let kept = st.k.depth <= 4 in
    let base_a = if kept then ur_dbase_block + (2 * stage) else ur_dbase in
    let base_b = base_a + 1 in
    (* A deep ring keeps one pair of bases and moves them from stage to stage:
       the start field is the address over 16, so the next stage's is one add
       of the stages' distance over 16, as nvjet advances it (UIADD3 UR16,
       UR16, 0x3fa). The first stage a k loop emits builds them outright. *)
    if not kept
    then begin
      match st.desc_of with
      | Some prev ->
        let d = (stage - prev) * st.stage_bytes in
        if d mod 16 <> 0 then failwith "mma: a stage is not a whole number of 16-byte units";
        Sass.uiadd3 b base_a base_a (d / 16);
        Sass.uiadd3 b base_b base_b (d / 16)
      | None ->
        desc_low st ~ur:base_a ~off:(Hashtbl.find st.smem_dyn a + (stage * st.stage_bytes));
        desc_low st ~ur:base_b ~off:(Hashtbl.find st.smem_dyn bb + (stage * st.stage_bytes))
    end;
    st.desc_of <- Some stage;
    (* the tile's first k step overwrites every block; it reads a flag the
       loop body sets, every other step accumulates *)
    let first = st.mma_seen = 0 in
    if first then Sass.uisetp_ne b 0 ur_mma_count;
    let issue ~r ~j =
      Sass.uiadd3 b ur_db base_b (db.kstep * j);
      Sass.uiadd3 b ur_da base_a ((da.kstep * j) + a_rep r);
      let dst = if r = 0 then ur_acc else (Sass.uiadd3 b ur_acc_rep ur_acc (r * acc_span st.k acc); ur_acc_rep) in
      if first && j = 0
      then
        if two_cta st
        then Sass.utchmma2_up b ~guard:up_leader ~a:ur_da ~bb:ur_db ~d:dst ~e:ur_zero ~idesc:ur_idesc ~up:0
        else Sass.utchmma_up b ~a:ur_da ~bb:ur_db ~d:dst ~e:ur_zero ~idesc:ur_idesc ~up:0
      else if two_cta st
      then Sass.utchmma2 b ~guard:up_leader ~a:ur_da ~bb:ur_db ~d:dst ~e:ur_zero ~idesc:ur_idesc ~acc:true
      else Sass.utchmma_acc b ~a:ur_da ~bb:ur_db ~d:dst ~e:ur_zero ~idesc:ur_idesc ~acc:true
    in
    let reps = List.init acc.reps (fun r' -> if !mma_reverse then acc.reps - 1 - r' else r') in
    (* A stacked MMA takes the stage one block at a time, every k step of a
       block before the next block, as nvjet's 256 x 256 does; [mma_by_step]
       interleaves the blocks at each k step instead. *)
    if !mma_by_step
    then for j = 0 to steps - 1 do List.iter (fun r -> issue ~r ~j) reps done
    else List.iter (fun r -> for j = 0 to steps - 1 do issue ~r ~j done) reps;
    if first then Sass.umov b ur_mma_count 1;
    st.mma_seen <- st.mma_seen + steps
  | Commit p ->
    (* A stage the whole cluster refills is released to the whole cluster: the
       commit signals that barrier in every CTA the mask selects, and each CTA
       waits only on its own copy, which expects one arrival per CTA. *)
    (* A stage is released to every CTA whose copy the MMAs read, which is the
       whole cluster; an accumulator is ready only in the two CTAs the MMA
       split its rows over, which is the pair. *)
    let mask = if (pipe st p).cross then ur_mask_plain else ur_mask_b_plain in
    if two_cta st
    then Sass.utcbar2_mc st.b ~guard:up_leader ~mbar:(commit_bar st p ~stage ~buf) ~mask
    else if (pipe st p).cross && grid_cluster st.k
    then Sass.utcbar_mc st.b ~mbar:(commit_bar st p ~stage ~buf) ~mask
    else Sass.utcbar st.b ~mbar:(commit_bar st p ~stage ~buf)
  | Signal p -> release_to_pair st p ~stage ~buf
  | Store { dst; src; via; release } -> store_body st (store_plan st ~dst ~src ~via) ~release ~buf
  | Kloop body ->
    ignore buf;
    let b = st.b in
    let s = st.k.depth in
    let t = st.k.k_total / st.k.tile_k in
    (* The ring is continuous across tiles: this tile's k loop starts on the
       stage the previous one ended on, runs the head of the ring from there
       to its end, then whole passes, then the stages left over. *)
    let s0 = st.ring_start in
    let head = if s0 = 0 then 0 else min (s - s0) t in
    let rounds = (t - head) / s and tail = (t - head) mod s in
    let waited = List.filter_map (function Wait p -> Some p | _ -> None) body in
    let tmas = List.filter_map (function Tma { dst; src = _; rows; pipe = _ } -> Some (dst, rows) | _ -> None) body in
    List.iteri
      (fun i (dst, rows) ->
        let g = ur_tma.(i) in
        Sass.umov b (g + 2) 0;
        let origin = match rows with Tile_m -> ur_tile_m | Tile_n -> ur_tile_n in
        match rank_stride st ~dst ~rows with
        | 0 -> Sass.uiadd3 b (g + 3) origin 0
        | stride when pow2 stride -> Sass.ulea b (g + 3) ur_rank_x origin (log2 stride)
        | stride -> Sass.uimad_imm b (g + 3) ur_rank_x stride origin)
      tmas;
    (match tmas with
     | [] -> ()
     | _ ->
       (* the bytes the loads deliver: each box's image, and for a pair the
          partner's boxes too, since they report to the same barrier *)
       let tx =
         List.fold_left
           (fun acc (dst, _) -> acc + footprint (Hashtbl.find st.layouts dst) ~elem:(elem_bytes (stile st dst).sdtype))
           0 tmas
       in
       let tx = if two_cta st then tx * st.k.cluster else tx in
       Sass.mov_imm b r_tmp2 tx);
    (match List.find_opt (function Mma _ -> true | _ -> false) body with
     | None -> ()
     | Some (Mma { atom; d; a; b = bb }) ->
       Sass.umov b ur_mma_count 0;
       Sass.umov b ur_zero 0;
       (* the accumulator holds the rows of the result the atom gives this CTA,
          and all its columns *)
       let acc = ttile st d in
       if acc.trows <> snd (share_rows atom `C ~v:0) || acc.tcols <> atom.n
       then failwith (d ^ ": the accumulator is not the result rows the atom gives a CTA");
       Sass.umov b ur_idesc (Atom.idesc atom);
       Sass.umov b (ur_da + 1) (Atom.desc_high (operand_desc st a));
       Sass.umov b (ur_db + 1) (Atom.desc_high (operand_desc st bb));
       if s <= 4
       then
         for stage = 0 to s - 1 do
           desc_low st ~ur:(ur_dbase_block + (2 * stage)) ~off:(Hashtbl.find st.smem_dyn a + (stage * st.stage_bytes));
           desc_low st ~ur:(ur_dbase_block + (2 * stage) + 1) ~off:(Hashtbl.find st.smem_dyn bb + (stage * st.stage_bytes))
         done
     | Some _ -> assert false);
    let mode =
      if !debug_waits then Probe_off
      else if List.exists (function Mma _ -> true | _ -> false) body
      then (match !probe_mma with Some m -> m | None -> if st.k.ask_ahead then Probe_early else Probe_off)
      else !probe_prod
    in
    let ask next = match next with
      | Some (next, wraps) -> List.iter (fun p -> if (pipe st p).per_stage then probe st p ~stage:next ~wraps) waited
      | None -> ()
    in
    let emit_stage ?(pending = false) ?next stage =
      let tx_done = Hashtbl.create 2 and tma_index = ref 0 in
      let pending = pending && mode <> Probe_off in
      st.probe_in <- pending;
      st.probe_next <- (if mode = Probe_early then next else None);
      List.iter (lower_stmt st ~stage ~buf ~tx_done ~tma_index) body;
      if mode = Probe_late then ask next;
      st.probe_in <- false;
      st.probe_next <- None
    in
    (* A stage barrier's phase is the number of passes the ring has made, so
       the one parity every stage shares flips each time the ring wraps past
       its last stage -- wherever the tile started. *)
    let wrap () =
      List.iter
        (fun p -> if (pipe st p).per_stage then (let r = r_parity.(Hashtbl.find st.pipe_index p) in Sass.lop3_xor_imm b r r 0x80000000))
        waited
    in
    st.mma_seen <- 0;
    st.desc_of <- None;
    (* the timing build notes when the tile's first stage has landed: a second
       wait on a phase that has completed passes at once *)
    if !stamps && List.mem "full" waited && List.exists (function Mma _ -> true | _ -> false) body
    then (lower_wait st "full" ~stage:s0 ~buf; stamp st 9);
    (* each stage asks about the one that runs after it: within a pass the
       next stage, past the last stage the first one of the next pass *)
    let after_head = rounds > 0 || tail > 0 in
    for stage = s0 to s0 + head - 1 do
      let next = if stage < s0 + head - 1 then Some (stage + 1, false) else if after_head then Some (0, true) else None in
      emit_stage ~pending:(stage > s0) ?next stage
    done;
    if head > 0 && s0 + head = s then wrap ();
    if rounds > 0 then begin
      if rounds > 1 then Sass.mov_rz b r_cnt;
      (* the loop's first stage reads an answer on every pass: the head's
         last stage asked, or it is asked here *)
      if head = 0 && mode <> Probe_off
      then List.iter (fun p -> if (pipe st p).per_stage then probe st p ~stage:0 ~wraps:false) waited;
      let l = new_label st "KLOOP" in
      Sass.label b l;
      for stage = 0 to s - 1 do
        emit_stage ~pending:true ~next:(if stage < s - 1 then stage + 1, false else 0, true) stage
      done;
      wrap ();
      if rounds > 1 then begin
        Sass.viadd b r_cnt r_cnt 1;
        Sass.isetp_lt_u32_imm b p_loop r_cnt rounds;
        Sass.bra b p_loop l
      end
    end;
    (* the k tiles left over: the first [tail] stages of one more pass, with the
       parities the loop left behind; the next tile starts where they end *)
    for stage = 0 to tail - 1 do
      emit_stage ~pending:(stage > 0 || rounds > 0 || head > 0) ?next:(if stage < tail - 1 then Some (stage + 1, false) else None) stage
    done
  | Role _ -> failwith "nested role"
  | Schedule -> failwith "the scheduler is a role of its own"

(* Free [ncols] tensor-memory columns allocated at address [base]: clear
   their 32-column chunks and the allocation's start bit, 16 above its first
   chunk -- the mask ptxas builds (ref/talloc512.ptx). *)
let free_tmem b ~base ~ncols =
  let u = ur_init in
  Sass.ulop3_and b u base 0xffff;
  Sass.ushf_r b u u 5;
  Sass.umov b (u + 1) ((1 lsl (ncols / 32)) - 1);
  Sass.ushf_l_ur b (u + 1) (u + 1) u;
  Sass.uiadd3 b ur_tmp u 16;
  Sass.umov b ur_zero 1;
  Sass.ushf_l_ur b ur_zero ur_zero ur_tmp;
  Sass.ulop3_or_ur b (u + 1) (u + 1) ur_zero;
  Sass.ulop3_not b (u + 1) (u + 1);
  Sass.utcatomsws_and b (u + 1)

(* Allocate [ncols] columns: the allocator answers in [ur_init] and sets UP0
   when it found them; until it does, wait and ask again. *)
let alloc_tmem ?(tag = "") b ~ncols =
  let l x = x ^ tag in
  (* one lane asks, as ptxas has it: the others wait at the warp sync below *)
  Sass.elect b p_loop;
  Sass.bra b ~neg:true p_loop (l "ALLOC_SYNC");
  Sass.label b (l "ALLOC");
  Sass.umov b ur_init (ncols / 32);
  Sass.depbar_sb0 b;
  Sass.utcatomsws_fas b ur_init;
  Sass.plop3_up0 b 0;
  Sass.bra b 0 (l "ALLOC_OK");
  Sass.nanosleep b;
  Sass.jmp b (l "ALLOC");
  Sass.label b (l "ALLOC_OK");
  Sass.ushf_l b ur_init ur_init 5;
  Sass.label b (l "ALLOC_SYNC");
  Sass.warpsync b

(* Each accumulator buffer is its own allocation, its address in its own slot
   word. One allocation of all 512 columns is refused by the next launch on the
   SM once it has been freed -- measured, with nothing but an allocate and a
   free in the kernel (warpc talloc 512) -- while two of 256, or four of 128,
   come back clean every time. *)
let buffer_base st ~buf ~into =
  Sass.lds st.b r_tmp ~ur:ur_smem ~imm:(st.slot_off - 0x400 + (4 * buf));
  Sass.r2ur st.b into r_tmp

let dealloc st =
  let acc = List.hd st.k.tmem in
  let ncols = Atom.tmem_columns (acc.reps * acc_span st.k acc) in
  (* An allocation of all 512 columns is freed by clearing the allocator's
     whole map, as nvjet does: clearing its columns alone leaves the next
     launch on the SM waiting forever (measured, warpc talloc 512 [clear]).
     Only a CTA alone on its multiprocessor holds all 512. *)
  if ncols * acc.bufs = 512 && acc.bufs = 1
  then Sass.utcatomsws_clear st.b
  else
    for buf = 0 to acc.bufs - 1 do
      buffer_base st ~buf ~into:ur_acc;
      free_tmem st.b ~base:ur_acc ~ncols
    done

(* ---- cluster launch control ---- *)

(* The answer ring's barriers are addressed through a register, [Rn+URZ], as
   ptxas addresses barriers it indexes at run time: a uniform register that
   names different barriers at different points is refused by the device
   (an illegal instruction at the barrier operation, found by bisection). *)
let r_clc_addr = 9 and r_clc_ans = 20 (* the answer, four registers *)

(* how the CLC code addresses its barriers and reads its answer -- switches
   for bisecting it on the device *)
type clc_style =
  { gpr_bars : bool (* barriers as [Rn+URZ], else each slot's own uniform register *)
  ; wide : bool (* the answer by one LDS.128, else word by word *)
  ; cluster_ops : bool (* the request's operands as shared::cluster addresses, else window offsets *)
  }

(* Measured on the device with the tile-loop probe (warpc pclcloop): the
   answer must be read by one 128-bit load -- word by word, a taker sees no
   cluster where there was one and ~half the tiles are never done -- and the
   request's operands must be window offsets: as shared::cluster addresses
   the request never completes. The barriers work either way. *)
let clc_style = ref { gpr_bars = true; wide = true; cluster_ops = false }

(* this CTA's copy of a window offset, as a shared::cluster address *)
let local_addr st ~dst off =
  Sass.mov_ur st.b dst ur_smem;
  Sass.iadd3_c st.b dst dst (off - 0x400)

(* the window offset of a barrier slot *)
let slot_bar slot = 0x400 + (8 * slot)

(* wait on this CTA's barrier in [slot] *)
let wait_slot st ~addr ~slot ~parity =
  let l = new_label st "WAIT" in
  if !clc_style.gpr_bars then local_addr st ~dst:addr (slot_bar slot);
  Sass.label st.b l;
  if !clc_style.gpr_bars
  then Sass.syncs_trywait_r st.b 0 ~addr ~parity
  else (let base, imm = mbar_addr_of_slot slot in
        Sass.syncs_trywait st.b 0 ~base ~imm ~parity_reg:(Some parity));
  Sass.nanosleep_syncs st.b ~neg:true 0;
  Sass.bra st.b ~neg:true 0 l

(* read the answer at window offset [off]: its first word to [first], its
   validity bit to [valid] *)
let read_answer st ~addr ~off ~first ~valid =
  let b = st.b in
  if !clc_style.wide
  then begin
    local_addr st ~dst:addr off;
    Sass.lds128_r b r_clc_ans ~addr;
    (match first with Some r -> Sass.mov_rr b r r_clc_ans | None -> ());
    Sass.lop3_and b valid (r_clc_ans + 2) 1
  end
  else begin
    Sass.uiadd3 b ur_clc ur_smem (off - 0x400);
    (match first with Some r -> Sass.lds b r ~ur:ur_clc ~imm:0 | None -> ());
    Sass.lds b valid ~ur:ur_clc ~imm:8;
    Sass.lop3_and b valid valid 1
  end

(* The next tile, from the answer in ring slot [slot]: wait for it, read the
   first CTA of the cluster it cancelled and whether there was one, and give
   the slot back to the scheduler, whose barrier is in the cluster's first
   CTA. The tile is that cluster's CTA of this CTA's rank. *)
let clc_take st ~slot ~last ~tl_end =
  let b = st.b and n_ctas = ctas st.k in
  wait_slot st ~addr:r_clc_addr ~slot:(st.clc_full + slot) ~parity:r_clc;
  read_answer st ~addr:r_clc_addr ~off:(st.clc_resp + (16 * slot)) ~first:(Some r_tile) ~valid:r_resp;
  if n_ctas > 1 then Sass.lea_ur b r_tile r_tile ur_cta 0;
  if n_ctas > 1
  then begin
    (* the CTA field of a shared::cluster address is the rank: 0 is the first *)
    Sass.mov_imm b r_clc_addr (slot_bar (st.clc_empty + slot));
    Sass.syncs_arrive_red_r b ~guard:p_lane0 ~addr:r_clc_addr
  end
  else if !clc_style.gpr_bars
  then begin
    local_addr st ~dst:r_clc_addr (slot_bar (st.clc_empty + slot));
    Sass.syncs_arrive_r b ~guard:p_lane0 ~addr:r_clc_addr
  end
  else (let base, imm = mbar_addr_of_slot (st.clc_empty + slot) in
        Sass.syncs_arrive b ~guard:p_lane0 ~base ~imm);
  (* the ring's barriers complete a phase per pass over its slots *)
  if last then Sass.lop3_xor_imm b r_clc r_clc 0x80000000;
  Sass.isetp_eq_u32 b p_role r_resp 0;
  Sass.bra b p_role tl_end

(* The scheduler, in the cluster's first CTA: for each slot of the ring, once
   every warp that takes tiles has read the slot's last answer, state the 16
   bytes of the next one on each CTA's copy of the slot, cancel a cluster not
   yet launched (the answer is broadcast to the whole cluster), and read the
   answer too: when there was no cluster left, wait until the takers have
   read that answer and stop. *)
let r_sched_tx = 12 and r_sched_addr = 13

let schedule st ~role_end =
  let b = st.b and k = st.k in
  let n = match k.tiles with Clc n -> n | Stride -> failwith "Schedule: this kernel takes its tiles by stride" in
  let n_ctas = ctas k in
  if n_ctas > 1 then begin
    Sass.uisetp_eq0 b up_first ur_cta;
    Sass.plop3_up b p_loop ~up:up_first;
    Sass.bra b ~neg:true p_loop role_end
  end;
  Sass.mov_imm b r_clc_free 0x80000000;
  Sass.mov_imm b r_clc 0;
  Sass.mov_imm b r_sched_tx 16;
  let top = new_label st "SCHED" and stop = new_label st "SCHED_END" in
  let drains = List.init n (fun _ -> new_label st "SCHED_LAST") in
  Sass.label b top;
  for s = 0 to n - 1 do
    wait_slot st ~addr:r_sched_addr ~slot:(st.clc_empty + s) ~parity:r_clc_free;
    for v = 0 to n_ctas - 1 do
      if n_ctas > 1
      then begin
        Sass.mov_imm b r_sched_addr ((v lsl 24) + slot_bar (st.clc_full + s));
        Sass.syncs_arrive_tx_red_r b ~guard:p_lane0 ~addr:r_sched_addr ~tx:r_sched_tx
      end
      else if !clc_style.gpr_bars
      then begin
        local_addr st ~dst:r_sched_addr (slot_bar (st.clc_full + s));
        Sass.syncs_arrive_tx_r b ~guard:p_lane0 ~addr:r_sched_addr ~tx:r_sched_tx
      end
      else (let base, imm = mbar_addr_of_slot (st.clc_full + s) in
            Sass.syncs_arrive_tx b ~guard:p_lane0 ~base ~imm ~tx:r_sched_tx)
    done;
    if !clc_style.cluster_ops
    then begin
      Sass.uiadd3 b ur_st ur_smem (st.clc_resp - 0x400 + (16 * s));
      Sass.uiadd3 b (ur_st + 1) ur_smem (8 * (st.clc_full + s))
    end
    else begin
      Sass.umov b ur_st (st.clc_resp + (16 * s));
      Sass.umov b (ur_st + 1) (slot_bar (st.clc_full + s))
    end;
    (* a uniform instruction: the warp issues it once *)
    Sass.warpsync b;
    Sass.ugetnextworkid b ~resp:ur_st ~mbar:(ur_st + 1);
    wait_slot st ~addr:r_sched_addr ~slot:(st.clc_full + s) ~parity:r_clc;
    read_answer st ~addr:r_sched_addr ~off:(st.clc_resp + (16 * s)) ~first:None ~valid:r_resp;
    Sass.isetp_eq_u32 b p_loop r_resp 0;
    Sass.bra b p_loop (List.nth drains s)
  done;
  Sass.lop3_xor_imm b r_clc_free r_clc_free 0x80000000;
  Sass.lop3_xor_imm b r_clc r_clc 0x80000000;
  Sass.jmp b top;
  List.iteri
    (fun s l ->
      Sass.label b l;
      Sass.lop3_xor_imm b r_clc_free r_clc_free 0x80000000;
      wait_slot st ~addr:r_sched_addr ~slot:(st.clc_empty + s) ~parity:r_clc_free;
      Sass.jmp b stop)
    drains;
  Sass.label b stop

(* A probe of the allocator alone: warp 0 allocates [ncols] columns, gives up
   its permit, frees them and exits -- the GEMM's instructions and nothing
   else, so a launch that follows shows whether the free left anything. *)
let tmem_probe ?(clear = false) ~ncols ~times () =
  let b = Sass.create () in
  Sass.ldc b 1 0x37c;
  Sass.s2r_tid b r_tid;
  Sass.shf_r b r_warp r_tid 5;
  Sass.isetp_ne_u32 b p_role r_warp 0;
  Sass.bra b p_role "DONE";
  (* each allocation's address is kept in its own uniform register *)
  let keep = [| 1; 2; 3; 0 |] in
  for i = 0 to times - 1 do
    alloc_tmem ~tag:(string_of_int i) b ~ncols;
    Sass.uiadd3 b keep.(i) ur_init 0
  done;
  Sass.uvirtcount_dealloc b;
  if clear then Sass.utcatomsws_clear b
  else
    for i = 0 to times - 1 do
      free_tmem b ~base:keep.(i) ~ncols
    done;
  Sass.label b "DONE";
  Sass.exit b;
  [ Printf.sprintf ".kernel talloc_%dx%d" times ncols; ".sm sm_100a"; ".regs 16"; ".barriers 1"; ".threads 128"
  ; ".smem 1024"; ".mbarriers 1"; ".tcgen05"; ".params 8" ]
  @ Sched.schedule (Sass.items b)

(* A probe of the tile loop under cluster launch control, with this
   compiler's own scheduler and take: warp 0 takes tiles -- its first is its
   CTA's -- and writes its CTA's id + 1 to out[tile] for each; warp 2 is the
   scheduler. Every tile must be written exactly by the CTA that took it. *)
let clc_loop_probe ~first () =
  let b = Sass.create () in
  let k =
    { (Dsl2.gemm ~m:128 ~n:128 ~k:64 ~depth:1 ()) with
      tiles = Clc 2; body = [ Role ([ 0 ], []); Role ([ 2 ], [ Schedule ]) ] }
  in
  let st =
    { b; k; pipe_slot = Hashtbl.create 1; pipe_index = Hashtbl.create 1; smem_dyn = Hashtbl.create 1; stage_bytes = 0
    ; slot_off = 0x420; labels = 0; max_reg = 32; mma_seen = 0; ring_start = 0; desc_of = None; probe_in = false; probe_next = None; smem_base = ur_smem; epi_off = 0
    ; layouts = Hashtbl.create 1; copy_bytes = Hashtbl.create 1; clc_full = first; clc_empty = first + 2
    ; clc_resp = 0x400 + (8 * (first + 4)) + 16 }
  in
  Sass.ldc b 1 0x37c;
  Sass.s2r_tid b r_tid;
  Sass.s2r_ctaid b r_tile ~axis:"X";
  Sass.mov_rr b 12 r_tile;
  Sass.ldcu64 b ur_desc 0x358;
  Sass.ldcu64 b (ur_param 0) 0x380;
  Sass.shf_r b r_warp r_tid 5;
  Sass.lop3_and b r_lane r_tid 31;
  Sass.isetp_eq_u32 b p_lane0 r_lane 0;
  Sass.s2ur_cta b ur_cta;
  Sass.umov b ur_tmp 0x400;
  Sass.ulea b ur_smem ur_cta ur_tmp 0x18;
  for i = 0 to first + 3 do
    Sass.uiadd3 b (mbar_reg_of_slot i) ur_smem (8 * i)
  done;
  Sass.isetp_ne_u32 b p_role r_warp 1;
  Sass.bra b p_role "INIT_DONE";
  List.iter
    (fun (first, arrivals) ->
      Sass.umov b ur_init arrivals;
      Sass.uiadd3_neg b ur_init ur_init 0x100000;
      Sass.ushf_l b (ur_init + 1) ur_init 0xb;
      Sass.ushf_l b ur_init ur_init 0x1;
      for s = 0 to 1 do
        Sass.uiadd3 b ur_clc ur_smem (8 * (first + s));
        Sass.syncs_exch b ~base:ur_clc ~imm:0 ~v:ur_init
      done)
    [ first, 1; first + 2, 1 ];
  Sass.label b "INIT_DONE";
  Sass.membar_cta b;
  Sass.fence_view_async b;
  Sass.bar_sync b;
  (* warp 0 *)
  Sass.isetp_ne_u32 b p_role r_warp 0;
  Sass.bra b p_role "NOT_TAKER";
  Sass.mov_imm b r_clc 0;
  Sass.label b "TILES";
  for u = 0 to 1 do
    Sass.mov_ur b 20 (ur_param 0);
    Sass.mov_ur b 21 (ur_param 0 + 1);
    Sass.imad_wide b 20 r_tile 4 20;
    Sass.iadd3_c b 22 12 1;
    Sass.stg32 b ~base:20 ~imm:0 ~data:22;
    clc_take st ~slot:u ~last:(u = 1) ~tl_end:"TILES_END"
  done;
  Sass.jmp b "TILES";
  Sass.label b "TILES_END";
  Sass.exit b;
  Sass.label b "NOT_TAKER";
  Sass.isetp_ne_u32 b p_role r_warp 2;
  Sass.bra b p_role "IDLE";
  schedule st ~role_end:"IDLE";
  Sass.label b "IDLE";
  Sass.exit b;
  [ ".kernel clc"; ".sm sm_100a"; ".regs 40"; ".barriers 1"; ".threads 96"; ".smem 1024"
  ; Printf.sprintf ".mbarriers %d" (first + 4); ".params 8" ]
  @ Sched.schedule (Sass.items b)

let lower (k : kernel) : string list =
  let b = Sass.create () in
  let nthreads = 32 * k.nwarps in
  (* mbarrier slots and the TMEM slot in the static window after the reserved 0x400 *)
  let pipe_slot = Hashtbl.create 4 and pipe_index = Hashtbl.create 4 in
  let nslots = ref 0 in
  let nbuf = (List.hd k.tmem).bufs in
  List.iteri
    (fun i (p : pipe) ->
      Hashtbl.replace pipe_index p.pname i;
      Hashtbl.replace pipe_slot p.pname !nslots;
      nslots := !nslots + (if p.per_stage then k.depth else if p.per_buffer then nbuf else 1))
    k.pipes;

  (* the pipes' barriers each have a uniform register; the answer ring's are
     addressed where they are used, once a tile *)

  let clc_slots = match k.tiles with Clc n -> n | Stride -> 0 in
  let clc_full = !nslots in
  let clc_empty = clc_full + clc_slots in
  nslots := !nslots + (2 * clc_slots);
  let slot_off = 0x400 + (8 * !nslots) in
  let static_bytes = 0x400 in
  let clc_resp = round_up (slot_off + (4 * nbuf)) 16 in
  if clc_resp + (16 * clc_slots) > 0x400 + static_bytes then failwith "static shared memory overflow";
  (* offsets below are relative to the smem base register, which sits at window
     offset 0x400; the dynamic region begins right after the static bytes *)
  let dyn_base = static_bytes in
  (* Each shared tile's layout is fixed by the instruction that reads it. A
     copy takes its image's footprint, rounded up to the swizzle's period so
     that every copy starts where the pattern starts; the window offset of the
     dynamic region is itself a multiple of the period. *)
  if (0x400 + dyn_base) mod Atom.sw128_period <> 0 then failwith "the dynamic region is not swizzle-aligned";
  let layouts = Hashtbl.create 4 and copy_bytes = Hashtbl.create 4 in
  List.iter
    (fun (t : stile) ->
      let l = tile_layout k t in
      Hashtbl.replace layouts t.sname l;
      Hashtbl.replace copy_bytes t.sname (round_up (footprint l ~elem:(elem_bytes t.sdtype)) Atom.sw128_period))
    k.smem;
  (* the ring: one stage holds a copy of every stage tile, stages back to back *)
  let smem_dyn = Hashtbl.create 2 in
  let off = ref 0 in
  List.iter
    (fun (t : stile) ->
      if t.ring = Stages then begin
        Hashtbl.replace smem_dyn t.sname (dyn_base + !off);
        off := !off + Hashtbl.find copy_bytes t.sname
      end)
    k.smem;
  let stage_bytes = !off in
  (* after the ring, the staging tile: its copies for each warp that writes it *)
  let writers name =
    List.fold_left
      (fun acc s ->
        match s with
        | Role (ws, body) when reads (function Store { via; _ } -> via = name | _ -> false) body -> acc + List.length ws
        | _ -> acc)
      0 k.body
  in
  let epi_bytes =
    List.fold_left
      (fun acc (t : stile) ->
        match t.ring with
        | Stages -> acc
        | Per_warp n ->
          if acc > 0 then failwith "one staging tile per kernel";
          writers t.sname * n * Hashtbl.find copy_bytes t.sname)
      0 k.smem
  in
  let dyn_bytes = (stage_bytes * k.depth) + epi_bytes in
  (* a B200 multiprocessor gives a CTA 227 KB of shared memory *)
  if dyn_bytes + static_bytes + 0x400 > 232448
  then failwith (Printf.sprintf "shared memory: %d bytes, the multiprocessor has 232448" (dyn_bytes + static_bytes + 0x400));
  (* each buffer is its own allocation, of the power of two that holds its
     blocks *)
  let acc_cols = let t = List.hd k.tmem in Atom.tmem_columns (t.reps * acc_span k t) in
  if acc_cols * nbuf > 512 then failwith "tmem columns";
  let st =
    { b; k; pipe_slot; pipe_index; smem_dyn; stage_bytes; slot_off; labels = 0; max_reg = r_data.(1) + 63; mma_seen = 0
    ; ring_start = 0; desc_of = None; probe_in = false; probe_next = None; clc_full; clc_empty; clc_resp
    ; smem_base = ur_smem; epi_off = dyn_base + (stage_bytes * k.depth); layouts; copy_bytes }
  in
  (* a store's warps read tensor memory through their lane quarters, so they
     must hold each quarter exactly once *)
  List.iter
    (function
      | Role (ws, body) when reads (function Store _ -> true | _ -> false) body ->
        if List.sort compare (List.map (fun w -> w mod 4) ws) <> [ 0; 1; 2; 3 ]
        then failwith "store: the warps must be one of each lane quarter"
      | _ -> ())
    k.body;
  let alloc_warp = 1 in
  (* prologue *)
  Sass.ldc b 1 0x37c;
  Sass.s2r_tid b r_tid;
  Sass.ldcu64 b ur_desc 0x358;
  List.iteri (fun i _ -> Sass.ldcu64 b (ur_param i) (0x380 + (8 * i))) k.params;
  Sass.s2ur_cta b ur_cta;
  Sass.umov b ur_tmp 0x400;
  Sass.ulea b ur_smem ur_cta ur_tmp 0x18;
  stamp_count_reset st;
  if !stage_stamps then Sass.mov_imm b r_stage_n 0;
  stamp st 0;
  (* The tile a CTA owns. The map from a CTA index to a tile is a layout: the
     index's digits -- the CTA's rank in its cluster, its place in a group of
     rows, the column, the group -- name the tile, so consecutive CTAs walk
     down [group] rows before moving across and the tiles in flight share
     their operand rows in L2. What is emitted is the decided strided form of
     the map from the index to each coordinate of the tile's origin. *)
  (* The CTAs one MMA spans hold neighbouring blocks of its result, so they
     sit on neighbouring tiles along the output coordinate the accumulator's
     rows stand for: down the rows, or -- when the MMA's A operand is the
     second matrix -- across the columns. *)
  let cluster_on_cols = match k.tmem with t :: _ -> acc_rows_coord k t.tname = Tile_n | [] -> false in
  let tiles_m, tiles_n =
    if cluster_on_cols then k.tile_m_count / k.cluster_n, k.tile_n_count / k.cluster
    else k.tile_m_count / k.cluster, k.tile_n_count / k.cluster_n
  in
  let group =
    let rec g n = if n * 2 <= tiles_m && n < 8 then g (n * 2) else n in
    let g = g 1 in
    if pow2 tiles_n && tiles_m mod g = 0 then g else 1
  in
  let width = k.tile_n_count in
  let cta_grid : (Space.thread_value, Space.logical) Layout.t =
    Layout.of_linear
      (Group
         (if cluster_on_cols
          then
            [ Axis { size = tiles_m / group; stride = group * k.cluster_n * width }
            ; Axis { size = tiles_n; stride = k.cluster }
            ; Axis { size = group; stride = k.cluster_n * width }
            ; Axis { size = k.cluster_n; stride = width }
            ; Axis { size = k.cluster; stride = 1 }
            ]
          else
            [ Axis { size = tiles_m / group; stride = group * k.cluster * width }
            ; Axis { size = tiles_n; stride = k.cluster_n }
            ; Axis { size = group; stride = k.cluster * width }
            ; Axis { size = k.cluster_n; stride = 1 }
            ; Axis { size = k.cluster; stride = width }
            ]))
  in
  let ntiles = k.tile_m_count * k.tile_n_count in
  if not (Layout.is_bijection_onto cta_grid ~size:ntiles) then failwith "the CTA-to-tile map misses a tile";
  let tile_of t = Layout.offset cta_grid (Coord.unflatten (Layout.shape cta_grid) t) in
  let origin name f =
    match Decide.strided_form ~shape:(Bound ntiles) ~offset:(function Coord.Idx t -> f (tile_of t) | Tuple _ -> assert false) with
    | Some e -> e
    | None -> failwith (name ^ ": the CTA-to-tile map has no strided form")
  in
  let e_row = origin "tile row" (fun i -> i / width * k.tile_m)
  and e_col = origin "tile column" (fun i -> i mod width * k.tile_n) in
  Sass.s2r_ctaid b r_tile ~axis:"X";
  let tile_indices () =
    let em = Emit.create b ~scratch in
    let range = function "c" -> ntiles | v -> failwith v
    and reg = function "c" -> r_tile | v -> failwith v in
    Emit.into em ~range ~reg e_row ~dst:r_tilem;
    Emit.into em ~range ~reg e_col ~dst:r_tilen;
    st.max_reg <- max st.max_reg em.high;
    Sass.r2ur b ur_tile_n r_tilen;
    Sass.r2ur b ur_tile_m r_tilem
  in
  Sass.shf_r b r_warp r_tid 5;
  Sass.lop3_and b r_lane r_tid 31;
  Sass.isetp_eq_u32 b p_lane0 r_lane 0;
  (* ptxas puts the CTA mask in the upper half of the register: a cluster of
     two is 0x30000, not 0x3 (ref/mcast.ptx, UMOV UR6, 0x30000). *)
  Sass.umov b ur_mask (((1 lsl ctas k) - 1) lsl 16);
  Sass.umov b ur_mask_plain ((1 lsl ctas k) - 1);
  if grid_cluster k
  then begin
    (* rank x picks the share of the atom's rows this CTA holds, rank y the
       pair's block of the other output coordinate *)
    Sass.ulop3_and b ur_rank_x ur_cta (k.cluster - 1);
    Sass.ushf_r b ur_rank_y ur_cta (log2 k.cluster);
    (* the A group: every CTA holding this share of A's rows, one per pair *)
    let row_bits = List.init k.cluster_n (fun j -> 1 lsl (j * k.cluster)) in
    Sass.umov b ur_mask_a (List.fold_left ( lor ) 0 row_bits);
    Sass.ushf_l_ur b ur_mask_a ur_mask_a ur_rank_x;
    (* the B group: the pair itself *)
    Sass.umov b ur_mask_b_plain ((1 lsl k.cluster) - 1);
    Sass.ushf_l b ur_tmp ur_rank_y (log2 k.cluster);
    Sass.ushf_l_ur b ur_mask_b_plain ur_mask_b_plain ur_tmp;
    Sass.ushf_l b ur_mask_b ur_mask_b_plain 16;
    Sass.ushf_l b ur_mask_a ur_mask_a 16;
    (* one CTA of each group issues the load that fills the whole group *)
    (* the partner of a pair differs only in the low rank bit *)
    Sass.ulop3_xor_imm b ur_tmp ur_cta 1;
    Sass.umov b ur_peer 0x400;
    Sass.ulea b ur_peer ur_tmp ur_peer 0x18;
    (* A two-CTA MMA reads both CTAs' stages, so it may not start until both
       have landed.  One barrier can say that and a local one cannot, so every
       load of the pair reports to the LEADER's copy: both CTAs arrive there
       for their own bytes and the leader alone waits on it. *)
    Sass.ulop3_and b ur_tmp ur_cta (lnot (k.cluster - 1) land 0xff);
    Sass.umov b ur_lead 0x400;
    Sass.ulea b ur_lead ur_tmp ur_lead 0x18;
    Sass.uisetp_eq0 b up_leader ur_rank_x;
    Sass.plop3_up b p_lead ~up:up_leader;
    Sass.uisetp_eq0 b up_issue_b ur_rank_x;
    Sass.uisetp_eq0 b up_issue_a ur_rank_y
  end;

  (* A uniform register a barrier operation names holds that barrier's
     address for the whole kernel: the device refuses an operation on a
     barrier through a register that has named another one, or served as
     scratch (an illegal instruction, found by bisection). So every slot's
     register is set here once, and a barrier addressed at run time goes
     through a general register instead. *)
  for i = 0 to min !nslots bar_regs - 1 do
    Sass.uiadd3 b (mbar_reg_of_slot i) ur_smem (8 * i)
  done;
  (* the allocating warp: mbarrier inits, TMEM *)
  let signalled name =
    let rec walk = function
      | Signal p -> p = name
      | Store { release = Some p; _ } -> p = name
      | Kloop body | Role (_, body) -> List.exists walk body
      | _ -> false
    in
    List.exists walk k.body
  in
  (* the grid counts CTAs, and a cluster holds one tile per CTA *)
  let total_tiles = tiles_m * tiles_n * ctas k in
  (* Persistent when there are more tiles than multiprocessors: each CTA walks
     the tiles a grid apart. A cluster walks them together -- its CTAs are
     consecutive and the grid is a multiple of the cluster, so they reach the
     same cluster tile at every step -- and the stage and accumulator
     handshakes span the tile boundaries, so a CTA can be a tile ahead of its
     partner only as far as the ring lets it. *)
  let clc = clc_slots > 0 in
  let grid = if clc || total_tiles <= Dsl2.sms then total_tiles else Dsl2.sms / ctas k * ctas k in
  (* with cluster launch control every CTA takes tiles until the scheduler
     finds none left *)
  let persistent = clc || grid < total_tiles in
  Sass.isetp_ne_u32 b p_role r_warp alloc_warp;
  Sass.bra b p_role "INIT_DONE";
  (* Fetch the tensor maps now, while the barriers are set up: the first load
     would otherwise wait on its descriptor. CUTLASS does the same in its
     first instructions. *)
  List.iteri (fun i (g : gmat) -> if g.via = Tmap then Sass.utmacctl_pf b ~map:(ur_param i)) k.params;
  List.iter
    (fun (p : pipe) ->
      let arrivals =
        (* a pipe the warps signal by hand is signalled once per CTA of the
           pair; a pipe the tensor core commits reaches the pair in one go *)
        if two_cta st
        then
          if p.cross then p.arrivals * k.cluster_n
          else if signalled p.pname then p.arrivals * k.cluster
          else p.arrivals
        else if p.cross then p.arrivals * ctas k
        else p.arrivals
      in
      Sass.umov b ur_init arrivals;
      Sass.uiadd3_neg b ur_init ur_init 0x100000;
      Sass.ushf_l b (ur_init + 1) ur_init 0xb;
      Sass.ushf_l b ur_init ur_init 0x1;
      let n = if p.per_stage then k.depth else if p.per_buffer then nbuf else 1 in
      for s = 0 to n - 1 do
        (let base, imm = mbar_addr st p.pname ~stage:s ~buf:s in
         Sass.syncs_exch b ~base ~imm ~v:ur_init)
      done)
    k.pipes;
  if clc then begin
    (* An answer is awaited by one arrival -- the scheduler's, stating the 16
       bytes to come -- and read by every warp that takes tiles, across the
       cluster: in a pair only the leader's tensor-core warp takes them, one
       per pair of the cluster. *)
    let takers =
      List.fold_left
        (fun acc s ->
          match s with
          | Role (ws, body) when not (List.mem Schedule body) ->
            let ctas_taking = if two_cta st && reads (function Mma _ -> true | _ -> false) body then k.cluster_n else ctas k in
            acc + (List.length ws * ctas_taking)
          | _ -> acc)
        0 k.body
    in
    List.iter
      (fun (first, arrivals) ->
        Sass.umov b ur_init arrivals;
        Sass.uiadd3_neg b ur_init ur_init 0x100000;
        Sass.ushf_l b (ur_init + 1) ur_init 0xb;
        Sass.ushf_l b ur_init ur_init 0x1;
        for s = 0 to clc_slots - 1 do
          let base, imm = mbar_addr_of_slot (first + s) in
          Sass.syncs_exch b ~base ~imm ~v:ur_init
        done)
      [ clc_full, 1; clc_empty, takers ]
  end;
  Sass.label b "INIT_DONE";
  (* A CTA arrives on its partners' barriers, so none may start before every
     CTA of the cluster has initialised its own. The arrival publishes this
     CTA's, once every initialisation has completed, and the wait comes after
     the allocation below, just before the roles: nvjet's UCGABAR_ARV and
     UCGABAR_WAIT, and what ptxas makes of fence.mbarrier_init with a cluster
     barrier -- no memory barrier, no fence (ref/binit.ptx). Without a cluster
     the CTA's barrier does the same. *)
  if grid_cluster k then Sass.cluster_arrive_inits b else Sass.bar_sync_inits b;
  stamp st 1;
  (* The barriers are visible to every warp from here, so the producer starts
     loading now; tensor memory is allocated meanwhile, and only the warps that
     use it wait for it, at the start of their roles. *)
  Sass.isetp_ne_u32 b p_role r_warp alloc_warp;
  Sass.bra b p_role "ALLOC_DONE";
  for buf = 0 to nbuf - 1 do
    alloc_tmem ~tag:(string_of_int buf) b ~ncols:acc_cols;
    Sass.mov_ur b r_tmp ur_init;
    Sass.sts_ur b ~ur:ur_smem ~imm:(slot_off - 0x400 + (4 * buf)) ~data:r_tmp
  done;
  Sass.uvirtcount_dealloc b;
  Sass.label b "ALLOC_DONE";
  if grid_cluster k then Sass.cluster_wait b;
  (* the roles whose warps touch tensor memory: the MMA's and the store's *)
  let uses_tmem body = reads (function Mma _ | Store _ | Commit _ -> true | _ -> false) body in
  let tmem_warps =
    List.fold_left (fun acc s -> match s with Role (ws, body) when uses_tmem body -> acc + List.length ws | _ -> acc) 0 k.body
  in
  if not (List.exists (function Role (ws, body) -> uses_tmem body && List.mem alloc_warp ws | _ -> false) k.body)
  then failwith "the warp that allocates tensor memory must be one that uses it";
  (* roles *)
  List.iter
    (function
      | Role (ws, body) when List.mem Schedule body ->
        if body <> [ Schedule ] then failwith "the scheduler's role does nothing else";
        let skip = new_label st "ROLE_END" in
        let lo = List.fold_left min max_int ws and hi = List.fold_left max min_int ws in
        if lo <> hi then failwith "the scheduler is one warp";
        if lo > 0 then begin Sass.isetp_lt_u32_imm b p_role r_warp lo; Sass.bra b p_role skip end;
        Sass.isetp_lt_u32_imm b p_role r_warp (hi + 1);
        Sass.bra b ~neg:true p_role skip;
        let done_ = new_label st "SCHED_DONE" in
        (* the scheduler leaves once the takers have read its last answer *)
        schedule st ~role_end:done_;
        Sass.label b done_;
        Sass.exit b;
        Sass.label b skip
      | Role (ws, body) ->
        let skip = new_label st "ROLE_END" in
        let lo = List.fold_left min max_int ws and hi = List.fold_left max min_int ws in
        if List.length ws <> hi - lo + 1 then failwith "role warps must be a contiguous range";
        if lo > 0 then begin Sass.isetp_lt_u32_imm b p_role r_warp lo; Sass.bra b p_role skip end;
        Sass.isetp_lt_u32_imm b p_role r_warp (hi + 1);
        Sass.bra b ~neg:true p_role skip;
        (* every barrier this role waits on keeps its phase across tiles, so the
           parity lives in a register set once, before the tile loop *)
        let rec waits acc = function
          | [] -> acc
          | Wait p :: r -> waits (if List.mem p acc then acc else p :: acc) r
          | Kloop body :: r -> waits (waits acc body) r
          | _ :: r -> waits acc r
        in
        List.iter
          (fun p -> Sass.mov_imm b r_parity.(Hashtbl.find st.pipe_index p) (if (pipe st p).free_at_start then 0x80000000 else 0))
          (List.rev (waits [] body));
        (* a role that takes its tiles from the scheduler waits for its first answer *)
        if clc then Sass.mov_imm b r_clc 0;
        (* One pass of the tile loop covers one accumulator buffer each, so a
           barrier belonging to a buffer completes exactly once per pass, and
           its parity flips once per pass like a stage barrier. A CTA that runs
           out of tiles part way through a pass skips the rest of it. *)
        (* a store's tile-invariant addresses, once, before the first tile *)
        let rec stores acc = function
          | Store { dst; src; via; _ } -> (dst, src, via) :: acc
          | Kloop b | Role (_, b) -> List.fold_left stores acc b
          | _ -> acc
        in
        List.iter (fun (dst, src, via) -> store_setup st (store_plan st ~dst ~src ~via)) (List.fold_left stores [] body);
        (* the tensor-memory users wait here for the allocation; the named
           barrier also makes its slot words visible to them *)
        if uses_tmem body then Sass.bar_sync_n b ~bar:1 ~count:(32 * tmem_warps);
        let ev_start, ev_end =
          if reads (function Store _ -> true | _ -> false) body then 6, 8
          else if reads (function Mma _ -> true | _ -> false) body then 4, 5
          else 2, 3
        in
        stamp st ev_start;
        let tl = new_label st "TILES" in
        let tl_end = new_label st "TILES_END" in
        (* In a pair, the MMA and every stage barrier it waits on are the
           leader's. The other CTA's tensor-core warp has nothing to issue and
           nothing that completes for it to wait on, so it goes straight to the
           end of its role -- where it still meets the warps that use tensor
           memory and frees its own. *)
        if two_cta st && reads (function Mma _ -> true | _ -> false) body then Sass.bra b ~neg:true p_lead tl_end;
        (* A role that runs the ring starts each tile's k loop where the last one
           ended, so its tile loop is unrolled until the start comes round
           again as well as the buffers: every body then has its ring position
           at compile time. *)
        let runs_ring = List.exists (function Kloop _ -> true | _ -> false) body in
        let t = k.k_total / k.tile_k in
        let period = if runs_ring && persistent then k.depth / gcd t k.depth else 1 in
        (* and, taking tiles from the scheduler, until the answer ring's slot
           comes round *)
        let unroll = lcm (lcm nbuf period) (max 1 clc_slots) in
        (* A role leaves only once everything it handed out has come back:
           for each barrier it waits on that starts free -- a stage it filled,
           an accumulator it wrote -- it waits for the phase its next use
           would, so the arrivals that return them, the only ones still in
           flight towards its CTA, have landed. That is what lets a CTA leave
           without meeting its cluster. Each way out of the tile loop knows
           the tile it would have run next, [next], and with it the ring's
           position and the buffer. *)
        let rec all_waits acc = function
          | [] -> acc
          | Wait p :: r -> all_waits (if List.mem p acc then acc else p :: acc) r
          | Kloop b :: r -> all_waits (all_waits acc b) r
          | _ :: r -> all_waits acc r
        in
        let returned = List.filter (fun p -> (pipe st p).free_at_start) (List.rev (all_waits [] body)) in
        let drain ~next =
          List.iter
            (fun p ->
              let pp = pipe st p in
              let r = r_parity.(Hashtbl.find st.pipe_index p) in
              let n, first =
                if pp.per_stage then k.depth, (if runs_ring then next * t mod k.depth else 0)
                else if pp.per_buffer then nbuf, next mod nbuf
                else 1, 0
              in
              for i = first to n - 1 do lower_wait st p ~stage:i ~buf:i done;
              if first > 0 then begin
                Sass.lop3_xor_imm b r r 0x80000000;
                for i = 0 to first - 1 do lower_wait st p ~stage:i ~buf:i done
              end)
            returned
        in
        let exits = ref [] in
        let exit_before next = let l = new_label st "LEAVE" in exits := (l, next) :: !exits; l in
        if persistent then Sass.label b tl;
        for u = 0 to unroll - 1 do
          let buf = u mod nbuf in
          st.ring_start <- (if runs_ring then u * t mod k.depth else 0);
          if u > 0 && not clc then begin
            Sass.isetp_lt_u32_imm b p_role r_tile total_tiles;
            Sass.bra b ~neg:true p_role (exit_before u)
          end;
          tile_indices ();
          if uses_tmem body then buffer_base st ~buf ~into:ur_acc;
          List.iter (lower_stmt st ~stage:0 ~buf ~tx_done:(Hashtbl.create 1) ~tma_index:(ref 0)) body;
          stamp st (ev_start / 2 + 11);
          stamp_count_next st;
          (* a buffer's barrier completes once per pass over the buffers *)
          if buf = nbuf - 1
          then
            List.iter
              (fun p ->
                if (pipe st p).per_buffer
                then (let r = r_parity.(Hashtbl.find st.pipe_index p) in Sass.lop3_xor_imm b r r 0x80000000))
              (List.rev (waits [] body));
          if clc
          then clc_take st ~slot:(u mod clc_slots) ~last:(u mod clc_slots = clc_slots - 1) ~tl_end:(exit_before (u + 1))
          else Sass.iadd3_c b r_tile r_tile grid
        done;
        if persistent then
          if clc then Sass.jmp b tl
          else begin
            Sass.isetp_lt_u32_imm b p_role r_tile total_tiles;
            Sass.bra b p_role tl
          end;
        if not (persistent && clc) then drain ~next:unroll;
        if !exits <> [] then begin
          Sass.jmp b tl_end;
          List.iter
            (fun (l, next) ->
              Sass.label b l;
              drain ~next;
              Sass.jmp b tl_end)
            (List.rev !exits)
        end;
        Sass.label b tl_end;
        (* Tensor memory is freed only once nothing can touch it: the MMAs have
           completed and every warp that reads the accumulator has read it.
           The warps that use it meet here first. Freeing it any earlier --
           as soon as the MMA warp has issued its last MMA -- leaves columns
           allocated on the SM after the CTA exits, and the next launch that
           asks for the whole of tensor memory waits for them forever. *)
        (* a warp's last tensor-map stores must have read its staging copies
           before the warp leaves the shared memory they sit in *)
        if reads (function Store _ -> true | _ -> false) body then Sass.depbar_drain b;
        stamp st ev_end;
        if uses_tmem body then Sass.bar_sync_n b ~bar:1 ~count:(32 * tmem_warps);
        if lo <= alloc_warp && alloc_warp <= hi then dealloc st;
        if ev_start = 6 then stamp st 10;
        Sass.exit b;
        Sass.label b skip
      | _ -> failwith "top level must be roles")
    k.body;
  Sass.exit b;
  let nregs = round_up (st.max_reg + 1 + 2) 8 in
  (* Every tensor map the kernel takes, as the host must encode it: the box is
     read off the layout of the shared tile the matrix moves through, so the
     host cannot disagree with the addresses the kernel computes. *)
  let tmaps =
    List.filter_map
      (fun (g : gmat) ->
        if g.via <> Tmap
        then None
        else (
          let tiles =
            List.sort_uniq compare
              (let rec walk acc = function
                 | Tma { src; dst; _ } when src = g.name -> dst :: acc
                 | Store { dst; via; _ } when dst = g.name -> via :: acc
                 | Kloop body | Role (_, body) -> List.fold_left walk acc body
                 | _ -> acc
               in
               List.fold_left walk [] k.body)
          in
          match tiles with
          | [ t ] ->
            let bx = Atom.tma_box (Hashtbl.find layouts t) ~elem:(elem_bytes g.dtype) in
            Some
              (Printf.sprintf ".tmap %s %d %d %d %d %d %d" g.name g.rows g.cols bx.box_elem bx.box_rows bx.box_cols
                 bx.box_swizzle)
          | [] ->
            (* the kernel never reads this map (a probe that leaves the matrix
               alone), so the host only needs something valid to encode: one
               row of one swizzle span *)
            let e = elem_bytes g.dtype in
            Some (Printf.sprintf ".tmap %s %d %d %d 1 %d %d" g.name g.rows g.cols e (Atom.sw128_span / e) Atom.sw128_span)
          | _ -> failwith (g.name ^ ": moved through tiles with different layouts")))
      k.params
  in
  let header =
    List.map (fun l -> "# " ^ l) (String.split_on_char '\n' (Dsl2.to_string k))
    @ [ ".kernel " ^ k.name; ".sm sm_100a"; Printf.sprintf ".regs %d" nregs
      ; ".barriers 2"
      ; Printf.sprintf ".threads %d" nthreads; Printf.sprintf ".smem %d" static_bytes; Printf.sprintf ".dynsmem %d" dyn_bytes
      ; Printf.sprintf ".tile %d %d %d" k.tile_m k.tile_n k.tile_k
      ] @ tmaps @ [
      Printf.sprintf ".grid %d 1" grid; Printf.sprintf ".mbarriers %d" !nslots
      ; Printf.sprintf ".cluster %d" (ctas k)
      ; ".tcgen05"
      ; ".params " ^ String.concat " " (List.map (fun _ -> "8") k.params @ if !debug_waits || !stamps || !stage_stamps then [ "8" ] else []) ]
    @ (if !debug_waits then ".debug" :: List.rev_map (fun l -> "# " ^ l) !debug_sites else [])
    @ (if !stamps then ".debug" :: ".stamps" :: List.map (fun (i, s) -> Printf.sprintf "# stamp %d: %s" i s) stamp_names else [])
    @ (if !stage_stamps then [ ".debug"; ".stagestamps" ] else [])
  in
  header @ Sched.schedule (Sass.items b)
