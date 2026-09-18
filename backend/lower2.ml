(* Lowering of the second DSL: TMA into a ring of swizzled shared-memory
   stages, tcgen05 MMA out of them into tensor memory, mbarrier pipes
   between the roles, one CTA per output tile. *)

open Dsl2

let round_up a m = (a + m - 1) / m * m
let pow2 n = n > 0 && n land (n - 1) = 0

(* the smallest shift whose reciprocal divides exactly over [0, bound): the
   divisor is a tile count known at compile time, so this is a search, not an
   approximation, and it fails loudly rather than quietly rounding *)
let exact_recip d bound =
  let rec search sh =
    if sh > 30 then failwith "no exact reciprocal for the tile count"
    else
      let m = ((1 lsl sh) / d) + 1 in
      let rec ok t = t >= bound || ((t * m) lsr sh = t / d && ok (t + 1)) in
      if m * (bound - 1) < 0x40000000 && ok 0 then (m, sh) else search (sh + 1)
  in
  search 1
let rec log2 n = if n <= 1 then 0 else 1 + log2 (n / 2)
let elem_bytes = function F16 -> 2 | F32 -> 4

(* registers *)
let r_tid = 0 and r_warp = 2 and r_lane = 3 and r_tmp = 4 and r_cnt = 8 and r_tmp2 = 9
let r_caddr = 10 and r_tilen = 12 and r_tilem = 13 and r_tile = 14 and r_stage = 144 and r_stage2 = 145 and r_ptr = 146 and r_lrow = 148 and r_lcol = 149 and r_rows = 152 and r_back = 184 and r_swz = 216
let r_parity = [| 5; 6; 7; 15 |] (* one parity register per pipe, by declaration order *)
let r_data = [| 16; 80 |] (* two 64-register epilogue buffers *)
let p_role = 1 and p_lane0 = 2 and p_loop = 3 and p_lead = 4

(* uniform registers *)
let ur_desc = 4 and ur_param i = 8 + (2 * i)
let ur_cta = 14 and ur_tmp = 15 and ur_smem = 16 and ur_tmem = 17 and ur_tile_n = 18 and ur_tile_m = 19
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
let ur_wid = 23 (* this warp's index within the epilogue group *)

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
  ; mutable labels : int
  ; mutable max_reg : int
  ; mutable mma_seen : int (* MMAs emitted in the current loop body *)
  }

let new_label st p = st.labels <- st.labels + 1; Printf.sprintf "%s_%d" p st.labels

(* One MMA covers the accumulators of a CTA pair: the leader issues it, and the
   operands are each CTA's own rows of A with the columns of B they share. *)
let two_cta st = st.k.cluster = 2 && Sys.getenv_opt "WARPC_MMA2CTA" <> None

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

let mbar_reg_of_slot slot =
  if slot < 8 then 26 + slot else if slot < 20 then 52 + (slot - 8) else failwith "out of barrier registers"

let mbar_reg st p ~stage ~buf =
  let slot = mbar_slot st p ~stage ~buf in
  if slot < 8 then 26 + slot else if slot < 20 then 52 + (slot - 8) else failwith "out of barrier registers" 
let stage_bytes_of (s : stile) = s.srows * s.scols * elem_bytes s.sdtype

(* the 128-byte swizzled K-major UMMA descriptor of a tile starting at
   window offset [off] (the swizzle atom is 8 rows x 128 bytes; SBO = 1024).
   The address sits in the low word; the shape fields never change. *)
let desc_high = (1024 lsr 4) lor (1 lsl 14) lor (2 lsl 29)

let sw128_desc_low st ~ur ~off =
  let b = st.b in
  Sass.uiadd3 b ur ur_smem off;
  Sass.ushf_r b ur ur 4;
  Sass.ulop3_and b ur ur 0x3fff;
  Sass.ulop3_or b ur ur (1 lsl 16)

(* the descriptor of k chunk [j] of a stage: the base address plus 32 bytes
   per chunk, which is 2 in the descriptor's units *)
let sw128_descriptor st ~ur ~base ~j = Sass.uiadd3 st.b ur base (2 * j)

let lower_wait st p ~stage ~buf =
  let pp = pipe st p in
  let r = r_parity.(Hashtbl.find st.pipe_index p) in
  let l = new_label st "WAIT" in
  Sass.label st.b l;
  let pr = if pp.per_stage || Sys.getenv_opt "WARPC_LEGACY_PARITY" = None then Some r else None in
  Sass.syncs_trywait st.b 0 ~base:(mbar_reg st p ~stage ~buf) ~imm:0 ~parity_reg:pr;
  Sass.bra st.b ~neg:true 0 l;

  (* a barrier used once per tile completes a phase here; one used once per
     stage completes it when the k loop comes round, and flips there *)
  (* Barriers that belong to a group -- one per ring stage, one per accumulator
     buffer -- all advance one phase per pass over the group, so their shared
     parity flips once per pass, where the pass ends. A barrier used once per
     tile completes its phase right here. *)
  if (not pp.per_stage) && (not pp.per_buffer) && Sys.getenv_opt "WARPC_LEGACY_PARITY" = None
  then Sass.lop3_xor_imm st.b r r 0x80000000

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

let release_to_pair st p ~stage ~buf =
  Sass.syncs_arrive st.b ~guard:p_lane0 ~base:(mbar_reg st p ~stage ~buf) ~imm:0;
  if two_cta st && not (pipe st p).cross
  then begin
    Sass.uiadd3 st.b ur_peer_bar ur_peer (8 * mbar_slot st p ~stage ~buf);
    Sass.syncs_arrive_red st.b ~guard:p_lane0 ~base:ur_peer_bar ~imm:0
  end

let rec lower_stmt st ~stage ~buf ~(tx_done : (string, unit) Hashtbl.t) ~(tma_index : int ref) = function
  | Wait p -> lower_wait st p ~stage ~buf
  | Tma { dst; src; rows; pipe = p } ->
    let b = st.b in
    (* ptxas names the CTA's OWN barrier even for a .2CTA load, and states the
         whole box on it (ref/tma2cta.ptx) *)
    let bar_of _p = `Own (mbar_reg st p ~stage ~buf) in
    if not (Hashtbl.mem tx_done p) then begin
      Hashtbl.replace tx_done p ();
      (* the leader owns the barrier the pair's loads report to, so it alone
         states how many bytes to expect, and it states the pair's whole stage *)
      Sass.syncs_arrive_tx b ~guard:p_lane0 ~base:(mbar_reg st p ~stage ~buf) ~imm:0 ~tx:r_tmp2
    end;
    let g = ur_tma.(!tma_index) in
    incr tma_index;
    let base = Hashtbl.find st.smem_dyn dst + (stage * st.stage_bytes) in
    (* In a cluster every operand is needed by more than one CTA: the rows by
       the pairs working on neighbouring columns, the columns by the two CTAs a
       pair splits its rows over. One CTA of each group issues the load and
       multicasts it, so the bytes cross the memory system once per group
       instead of once per CTA, and the copy lands at the same offset in every
       CTA the mask names. *)
    let group =
      match rows with
      | Tile_m -> st.k.cluster_n (* the pairs working on neighbouring columns *)
      | Tile_n -> if two_cta st then 1 (* the pair splits the columns, so nobody shares *) else st.k.cluster
    in
    if grid_cluster st.k && group > 1
    then begin
      let mask, guard = match rows with Tile_m -> (ur_mask_a, up_issue_a) | Tile_n -> (ur_mask_b, up_issue_b) in
      Sass.uiadd3 b g ur_smem base;
      (match bar_of p with
       | `Own r -> Sass.uiadd3 b (g + 1) r 0
       | `Lead off -> Sass.uiadd3 b (g + 1) ur_lead off);
      Sass.utmaldg_mc ~guard ~two:(two_cta st) b ~g ~map:(ur_param (param_index st src)) ~mask
    end
    else begin
      Sass.uiadd3 b g ur_smem base;
      (match bar_of p with
       | `Own r -> Sass.uiadd3 b (g + 1) r 0
       | `Lead off -> Sass.uiadd3 b (g + 1) ur_lead off);
      Sass.utmaldg ~two:(two_cta st) b ~g ~map:(ur_param (param_index st src))
    end;
    Sass.uiadd3 b (g + 2) (g + 2) st.k.tile_k
  | Mma { d = _; a; b = bb } ->
    let b = st.b in
    let sa = stile st a and sb = stile st bb in
    let steps = st.k.tile_k / 16 in
    (* only the very first MMA of the kernel overwrites the accumulator; that
       one reads a flag the loop body sets, every other one accumulates *)
    let kept = st.k.depth <= 4 in
    let base_a = if kept then ur_dbase_block + (2 * stage) else ur_dbase in
    let base_b = base_a + 1 in
    if not kept
    then begin
      sw128_desc_low st ~ur:base_a ~off:(Hashtbl.find st.smem_dyn a + (stage * st.stage_bytes));
      sw128_desc_low st ~ur:base_b ~off:(Hashtbl.find st.smem_dyn bb + (stage * st.stage_bytes))
    end;
    for j = 0 to steps - 1 do
      sw128_descriptor st ~ur:ur_da ~base:base_a ~j;
      sw128_descriptor st ~ur:ur_db ~base:base_b ~j;
      if st.mma_seen = 0 then begin
        Sass.uisetp_ne b 0 ur_mma_count;
        (if two_cta st
         then Sass.utchmma2_up b ~guard:up_leader ~a:ur_da ~bb:ur_db ~d:ur_acc ~e:ur_zero ~idesc:ur_idesc ~up:0
         else Sass.utchmma_up b ~a:ur_da ~bb:ur_db ~d:ur_acc ~e:ur_zero ~idesc:ur_idesc ~up:0);
        Sass.umov b ur_mma_count 1
      end
      else if two_cta st
      then Sass.utchmma2 b ~guard:up_leader ~a:ur_da ~bb:ur_db ~d:ur_acc ~e:ur_zero ~idesc:ur_idesc ~acc:true
      else Sass.utchmma_acc b ~a:ur_da ~bb:ur_db ~d:ur_acc ~e:ur_zero ~idesc:ur_idesc ~acc:true;
      st.mma_seen <- st.mma_seen + 1
    done;
    ignore (sa, sb)
  | Commit p ->
    (* A stage the whole cluster refills is released to the whole cluster: the
       commit signals that barrier in every CTA the mask selects, and each CTA
       waits only on its own copy, which expects one arrival per CTA. *)
    (* A stage is released to every CTA whose copy the MMAs read, which is the
       whole cluster; an accumulator is ready only in the two CTAs the MMA
       split its rows over, which is the pair. *)
    let mask = if (pipe st p).cross then ur_mask_plain else ur_mask_b_plain in
    if two_cta st
    then Sass.utcbar2_mc st.b ~guard:up_leader ~mbar:(mbar_reg st p ~stage ~buf) ~mask
    else if (pipe st p).cross && grid_cluster st.k
    then Sass.utcbar_mc st.b ~mbar:(mbar_reg st p ~stage ~buf) ~mask
    else Sass.utcbar st.b ~mbar:(mbar_reg st p ~stage ~buf)
  | Signal p -> release_to_pair st p ~stage ~buf
  | Store { dst; src = _; release } ->
    let b = st.b in
    let c = gmat st dst in
    let tm = st.k.tile_m and tn = st.k.tile_n and ldc = c.cols in
    (* tensor memory: this warp's 32 lanes *)
    Sass.lop3_and b r_tmp r_warp 3;
    Sass.lea_ur b r_tmp2 r_tmp ur_acc 0x15;
    Sass.r2ur b ur_epi r_tmp2;
    (* Staging pays for itself only when enough tiles are in flight for the
       scattered stores to contend; with a handful of CTAs the machine has
       bandwidth to spare and the extra latency is all cost. *)
    let staged = st.k.tile_m_count * st.k.tile_n_count >= 64 in
    (* C address of this thread's row: ((tile_m*tm + 32*w4 + lane)*ldc + tile_n*tn) * 4 *)
    Sass.imad_rz b r_tmp2 r_tilem (tm * ldc * 4);
    Sass.lop3_and b r_tmp r_warp 3;
    Sass.imad b r_tmp2 r_tmp (32 * ldc * 4) r_tmp2;
    if staged
    then begin
      Sass.shf_r b r_lrow r_lane 4;
      Sass.lop3_and b r_lcol r_lane 15;
      Sass.imad b r_tmp2 r_lrow (ldc * 4) r_tmp2;
      Sass.imad b r_tmp2 r_lcol 16 r_tmp2
    end
    else Sass.imad b r_tmp2 r_lane (ldc * 4) r_tmp2;
    Sass.imad b r_tmp2 r_tilen (tn * 4) r_tmp2;
    Sass.iadd3_ur b r_caddr ~carry:0 r_tmp2 (ur_param (param_index st dst));
    Sass.imad_x_ur b (r_caddr + 1) (ur_param (param_index st dst) + 1) 0;
    (* Tensor memory hands a lane a whole row, so storing straight to global
       makes every lane of a warp touch a different cache line. The rows go
       through shared memory first and come back transposed, so a warp's store
       covers one contiguous run. Measured: this is a quarter of the runtime. *)
    (* Route two, shaped after CUTLASS's epilogue: read the accumulator in
       fragments, scatter them into a swizzled shared block, and let the copy
       engine write that block out. Two blocks per warp so a store overlaps the
       next fragment's staging. *)
    (* the accumulator goes back through shared memory either way; letting the
       copy engine read it out beats a warp doing the stores itself, and it is
       the only route that reaches the width the tensor pipe feeds at *)
    let tma_store = Sys.getenv_opt "WARPC_STAGED_EPILOGUE" = None in
    let chunks = if tma_store then tn / 32 else tn / 64 in
    let row_bytes = if tma_store then 32 * 4 else 64 * 4 in
    let pitch = if tma_store then row_bytes else row_bytes + 16 in
    let warp_stage = 32 * pitch in
    let epi_base = st.epi_off in
    (* this warp's staging area, the row this lane writes, and the 16 bytes of
       every row it reads back *)
    if staged then begin
    Sass.lop3_and b r_tmp r_warp 3;
    Sass.r2ur b ur_wid r_tmp;
    Sass.imad_rz b r_tmp r_tmp (if tma_store then 2 * warp_stage else warp_stage);
    Sass.imad b r_stage r_lane pitch r_tmp;
    Sass.lea_ur b r_stage r_stage ur_smem 0;
    Sass.iadd3_c b r_stage r_stage epi_base;
    (* A staged row holds 64 floats, which sixteen lanes cover with 16 bytes
       each, so the warp reads two rows at a time: the high half of the lane
       index picks the row, the low half the piece of it. *)
    Sass.shf_r b r_lrow r_lane 4;
    Sass.lop3_and b r_lcol r_lane 15;
    Sass.imad b r_stage2 r_lrow pitch r_tmp;
    Sass.imad b r_stage2 r_lcol 16 r_stage2;
    Sass.lea_ur b r_stage2 r_stage2 ur_smem 0;
    Sass.iadd3_c b r_stage2 r_stage2 epi_base;
    (* the rows a lane stores are a fixed stride apart and the stride is far
       past a store's offset field, so their addresses are built once here
       rather than walked inside every chunk *)
    if tma_store then begin
      (* piece p of a row sits at (p xor (row mod 8)) so the warp's writes land
         in different banks and the copy engine still sees its own layout *)
      Sass.lop3_and b r_tmp2 r_lane 7;
      for q = 0 to 7 do
        Sass.lop3_xor_imm_r b (r_swz + q) r_tmp2 q;
        Sass.imad b (r_swz + q) (r_swz + q) 16 r_stage
      done;
      st.max_reg <- max st.max_reg (r_swz + 7)
    end;
    Sass.mov_rr b r_rows r_caddr;
    Sass.mov_rr b (r_rows + 1) (r_caddr + 1);
    for pair = 1 to 15 do
      Sass.iadd3_imm b (r_rows + (2 * pair)) ~carry:0 (r_rows + (2 * pair) - 2) (2 * ldc * 4);
      Sass.imad_x_r b (r_rows + (2 * pair) + 1) (r_rows + (2 * pair) - 1) 0
    done;
    st.max_reg <- max st.max_reg (r_rows + 31)
    end;
    (* With two register buffers the whole accumulator can be read out before
       anything is written, which lets the tensor core have it back while this
       warp is still storing. *)
    (* Releasing the accumulator before the values are written lets the tensor
       core start the next tile while this warp stores. Measured: no gain, the
       stores are bandwidth-bound and overlapping does not make them cheaper,
       and holding both buffers plus a read-back scratch costs every register
       the thread has. Kept behind a flag. *)
    let early = release <> None && chunks <= 2 && Sys.getenv_opt "WARPC_EARLY_RELEASE" <> None in
    if early then begin
      for ch = 0 to chunks - 1 do
        let d = r_data.(ch mod 2) in
        Sass.ldtm_off b d ~n:(if tma_store then 32 else 64) ~addr:ur_epi ~imm:((if tma_store then 32 else 64) * ch);
        st.max_reg <- max st.max_reg (d + 63)
      done;
      match release with
      | Some p -> release_to_pair st p ~stage:0 ~buf
      | None -> ()
    end;
    for ch = 0 to chunks - 1 do
      let d = r_data.(ch mod 2) in
      if not early then begin
        Sass.ldtm_off b d ~n:(if tma_store then 32 else 64) ~addr:ur_epi ~imm:((if tma_store then 32 else 64) * ch);
        st.max_reg <- max st.max_reg (d + 63)
      end;
      if tma_store
      then begin
        (* the block this fragment goes to, alternating so the previous store
           can still be reading the other one *)
        let blk = (ch mod 2) * warp_stage in
        for q = 0 to 7 do
          Sass.sts_r b ~width:128 ~r:(r_swz + q) ~imm:blk ~data:(d + (4 * q))
        done;
        (* The copy engine reads the staging block, so the writes into it must
           have landed, not merely issued: a read scoreboard only says the
           store has taken its data out of the registers.  The fence publishes
           them to the async proxy and the wait has to come after it -- waiting
           first leaves the youngest stores unpublished and the engine reads
           the sixteen bytes they were about to overwrite. *)
        Sass.fence_view_async b;
        Sass.warpsync b;
        Sass.uiadd3 b ur_st ur_smem (epi_base + blk);
        Sass.ulea b ur_st ur_wid ur_st (log2 (2 * warp_stage));
        (* the store group is the block, then the two coordinates *)
        Sass.uiadd3 b (ur_st + 1) ur_tile_n (32 * ch);
        Sass.ulea b (ur_st + 2) ur_wid ur_tile_m 5;
        Sass.utmastg b ~g:ur_st ~map:(ur_param (param_index st dst));
        Sass.utmacmdflush b;
        Sass.depbar_drain b;
        Sass.warpsync b
      end
      else if not staged
      then
        for q = 0 to 15 do
          Sass.stg128 b ~base:r_caddr ~imm:((64 * ch * 4) + (16 * q)) ~data:(d + (4 * q))
        done
      else begin
      for q = 0 to 15 do
        Sass.sts_r b ~width:128 ~r:r_stage ~imm:(16 * q) ~data:(d + (4 * q))
      done;
      Sass.warpsync b;
      (* every read is independent, so they all go out before the first store
         waits on one: interleaving them leaves a single load in flight *)
      (* when both buffers hold accumulator values the read-back needs its own
         registers, not the other buffer *)
      let t = if early then r_back else r_data.((ch + 1) mod 2) in
      st.max_reg <- max st.max_reg (t + 63);
      for pair = 0 to 15 do
        Sass.lds_r b ~width:128 (t + (4 * pair)) ~r:r_stage2 ~imm:(2 * pair * pitch)
      done;
      for pair = 0 to 15 do
        Sass.stg128 b ~base:(r_rows + (2 * pair)) ~imm:(64 * ch * 4) ~data:(t + (4 * pair))
      done;
      Sass.warpsync b
      end
    done;
    if not early then (match release with
      | Some p -> release_to_pair st p ~stage:0 ~buf
      | None -> ())
  | Kloop body ->
    ignore buf;
    let b = st.b in
    let s = st.k.depth in
    let t = st.k.k_total / st.k.tile_k in
    let rounds = t / s and tail = t mod s in
    let waited = List.filter_map (function Wait p -> Some p | _ -> None) body in
    let tmas = List.filter_map (function Tma { dst; src = _; rows; pipe = _ } -> Some (dst, rows) | _ -> None) body in
    List.iteri
      (fun i (dst, rows) ->
        let g = ur_tma.(i) in
        Sass.umov b (g + 2) 0;
        match rows with
        | Tile_m -> Sass.uiadd3 b (g + 3) ur_tile_m 0
        | Tile_n ->
          if two_cta st
          then Sass.ulea b (g + 3) ur_rank_x ur_tile_n (log2 (stile st dst).srows)
          else Sass.uiadd3 b (g + 3) ur_tile_n 0)
      tmas;
    (match tmas with
     | [] -> ()
     | _ ->
       let tx = List.fold_left (fun acc (dst, _) -> acc + stage_bytes_of (stile st dst)) 0 tmas in
       (* measured: a .2CTA load still carries only the box this CTA asked for
          and reports it to this CTA's barrier, so the count is its own stage *)
       Sass.mov_imm b r_tmp2 tx);
    (match List.find_opt (function Mma _ -> true | _ -> false) body with
     | None -> ()
     | Some (Mma { a; b = bb; _ }) ->
       Sass.umov b ur_mma_count 0;
       Sass.umov b ur_zero 0;
       let dm = match Sys.getenv_opt "WARPC_IDESC_M" with Some v -> int_of_string v | None -> if two_cta st then 2 else 1 in
       let dn = match Sys.getenv_opt "WARPC_IDESC_N" with Some v -> int_of_string v | None -> 1 in
       let m_rows = st.k.tile_m * dm and n_cols = st.k.tile_n * dn in
       Sass.umov b ur_idesc ((1 lsl 4) lor ((n_cols lsr 3) lsl 17) lor ((m_rows lsr 4) lsl 24));
       Sass.umov b (ur_da + 1) desc_high;
       Sass.umov b (ur_db + 1) desc_high;
       if s <= 4
       then
         for stage = 0 to s - 1 do
           sw128_desc_low st ~ur:(ur_dbase_block + (2 * stage)) ~off:(Hashtbl.find st.smem_dyn a + (stage * st.stage_bytes));
           sw128_desc_low st ~ur:(ur_dbase_block + (2 * stage) + 1) ~off:(Hashtbl.find st.smem_dyn bb + (stage * st.stage_bytes))
         done
     | Some _ -> assert false);
    if rounds > 1 then Sass.mov_rz b r_cnt;
    let l = new_label st "KLOOP" in
    Sass.label b l;
    st.mma_seen <- 0;
    for stage = 0 to s - 1 do
      let tx_done = Hashtbl.create 2 and tma_index = ref 0 in
      List.iter (lower_stmt st ~stage ~buf ~tx_done ~tma_index) body
    done;
    (* every pass over the ring completes one phase of each stage barrier, so
       the parity flips here whether or not the pass is a loop iteration *)
    List.iter
      (fun p -> if (pipe st p).per_stage then (let r = r_parity.(Hashtbl.find st.pipe_index p) in Sass.lop3_xor_imm b r r 0x80000000))
      waited;
    if rounds > 1 then begin
      Sass.viadd b r_cnt r_cnt 1;
      Sass.isetp_lt_u32_imm b p_loop r_cnt rounds;
      Sass.bra b p_loop l
    end;
    (* the k tiles left over when the ring does not divide them: one more pass
       over the first [tail] stages, with the parities the loop left behind *)
    for stage = 0 to tail - 1 do
      let tx_done = Hashtbl.create 2 and tma_index = ref 0 in
      List.iter (lower_stmt st ~stage ~buf ~tx_done ~tma_index) body
    done
  | Role _ -> failwith "nested role"

let dealloc st =
  let b = st.b in
  let ncols = (List.hd st.k.tmem).tcols * (List.hd st.k.tmem).bufs in
  let u = ur_init in
  Sass.ulop3_and b u ur_tmem 0xffff;
  Sass.ushf_r b u u 5;
  Sass.umov b (u + 1) ((1 lsl (ncols / 32)) - 1);
  Sass.ushf_l_ur b (u + 1) (u + 1) u;
  Sass.uiadd3 b ur_tmp u 16;
  Sass.umov b ur_zero 1;
  Sass.ushf_l_ur b ur_zero ur_zero ur_tmp;
  Sass.ulop3_or_ur b (u + 1) (u + 1) ur_zero;
  Sass.ulop3_not b (u + 1) (u + 1);
  Sass.utcatomsws_and b (u + 1) 

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
  if !nslots > 20 then failwith "too many mbarriers for the uniform register map";
  let slot_off = 0x400 + (8 * !nslots) in
  let static_bytes = 0x400 in
  if slot_off + 4 > 0x400 + static_bytes then failwith "static shared memory overflow";
  (* offsets below are relative to the smem base register, which sits at window
     offset 0x400; the dynamic region begins right after the static bytes *)
  let dyn_base = static_bytes in
  (* stages: all tiles of one stage contiguous, 1024-aligned each *)
  let smem_dyn = Hashtbl.create 2 in
  let off = ref 0 in
  List.iter (fun (s : stile) -> Hashtbl.replace smem_dyn s.sname (dyn_base + !off); off := !off + round_up (stage_bytes_of s) 1024) k.smem;
  let stage_bytes = !off in
  (* the staging area exists only for the route that uses it *)
  let epi_bytes =
    if Sys.getenv_opt "WARPC_STAGED_EPILOGUE" = None
    then 4 * 2 * 32 * (32 * 4) (* two blocks per warp, 32 rows of 128 bytes *)
    else if k.tile_m_count * k.tile_n_count >= 64
    then 4 * 32 * ((64 * 4) + 16)
    else 0
  in
  let dyn_bytes = (stage_bytes * k.depth) + epi_bytes in
  let acc_cols = (List.hd k.tmem).tcols in
  let ncols = acc_cols * nbuf in
  if not (pow2 ncols && ncols >= 32 && ncols <= 512) then failwith "tmem columns";
  let st = { b; k; pipe_slot; pipe_index; smem_dyn; stage_bytes; slot_off; labels = 0; max_reg = r_data.(1) + 63; mma_seen = 0; smem_base = ur_smem; epi_off = dyn_base + (stage_bytes * k.depth) } in
  let alloc_warp = 1 in
  (* prologue *)
  Sass.ldc b 1 0x37c;
  Sass.s2r_tid b r_tid;
  Sass.ldcu64 b ur_desc 0x358;
  List.iteri (fun i _ -> Sass.ldcu64 b (ur_param i) (0x380 + (8 * i))) k.params;
  Sass.s2ur_cta b ur_cta;
  Sass.umov b ur_tmp 0x400;
  Sass.ulea b ur_smem ur_cta ur_tmp 0x18;
  (* The tile this CTA owns. The grid is one dimensional and the map from a
     CTA index to a tile is a layout: the index splits into digits (position
     within a group of rows, column, group), and the digits are shifts and
     masks. Consecutive CTAs walk down [group] rows before moving across, so
     the tiles running at any moment form a compact block and their operand
     rows stay in L2. *)
  let tiles_m = k.tile_m_count / k.cluster and tiles_n = k.tile_n_count / k.cluster_n in
  let group = if pow2 tiles_n then min tiles_m (min 8 (let rec g n = if n * 2 <= tiles_m && n < 8 then g (n * 2) else n in g 1)) else 1 in
  let rasterize = pow2 tiles_n && pow2 group && tiles_m mod group = 0 in
  Sass.s2r_ctaid b r_tile ~axis:"X";
  ignore rasterize;
  let tile_indices () =
    if grid_cluster k then Sass.shf_r b r_tmp r_tile (log2 (ctas k)) else Sass.imad_rz b r_tmp r_tile 1;
    if rasterize && (group > 1 || tiles_n > 1)
    then begin
    Sass.lop3_and b r_tilem r_tmp (group - 1);
    Sass.shf_r b r_tmp2 r_tmp (log2 group);
    Sass.lop3_and b r_tilen r_tmp2 (tiles_n - 1);
    Sass.shf_r b r_tmp2 r_tmp (log2 group + log2 tiles_n);
    Sass.imad b r_tilem r_tmp2 group r_tilem
  end
    else if pow2 tiles_n
    then begin
      Sass.lop3_and b r_tilen r_tmp (tiles_n - 1);
      Sass.shf_r b r_tilem r_tmp (log2 tiles_n)
    end
    else begin
      (* a column count that is not a power of two still splits the tile index
         exactly: the count is known here, so the reciprocal is chosen and
         checked over the whole range the kernel can see *)
      let m, sh = exact_recip tiles_n (tiles_m * tiles_n) in
      Sass.imad_rz b r_tilem r_tmp m;
      Sass.shf_r b r_tilem r_tilem sh;
      Sass.imad b r_tilen r_tilem (-tiles_n land 0xffffffff) r_tmp
    end;
    Sass.r2ur b ur_tile_n r_tilen;
    Sass.r2ur b ur_tile_m r_tilem;
    if grid_cluster k
    then begin
      (* the index decomposed above is the CLUSTER's tile; the rank names the
         tile inside it, x down the rows and y across the columns *)
      Sass.ushf_l b ur_tile_m ur_tile_m (log2 k.cluster);
      Sass.ulop3_and b ur_tmp ur_cta (k.cluster - 1);
      Sass.uiadd3_uu b ur_tile_m ur_tile_m ur_tmp;
      Sass.ushf_l b ur_tile_n ur_tile_n (log2 k.cluster_n);
      Sass.uiadd3_uu b ur_tile_n ur_tile_n ur_rank_y
    end;
    Sass.ushf_l b ur_tile_n ur_tile_n (log2 k.tile_n);
    Sass.ushf_l b ur_tile_m ur_tile_m (log2 k.tile_m)
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
    (* rank x picks the half of the rows this CTA holds, rank y the columns *)
    Sass.ulop3_and b ur_rank_x ur_cta (k.cluster - 1);
    Sass.ushf_r b ur_rank_y ur_cta (log2 k.cluster);
    (* the row group: every CTA holding these rows, one per pair *)
    let row_bits = List.init k.cluster_n (fun j -> 1 lsl (j * k.cluster)) in
    Sass.umov b ur_mask_a (List.fold_left ( lor ) 0 row_bits);
    Sass.ushf_l_ur b ur_mask_a ur_mask_a ur_rank_x;
    (* the column group: the pair itself *)
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

  for i = 0 to !nslots - 1 do
    Sass.uiadd3 b (if i < 8 then 26 + i else 52 + (i - 8)) ur_smem (8 * i)
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
  let grid =
    match Sys.getenv_opt "WARPC_GRID" with
    | Some g -> min total_tiles (int_of_string g)
    (* With a cluster, the CTAs of a cluster must stay on the same tile: a
       multicast writes into the partner's stage, so a partner that has moved
       on to another tile would receive the wrong rows. One tile per CTA keeps
       them together; persistence needs a cluster-wide barrier per tile. *)
    (* A clustered kernel is not persistent: the CTAs of a cluster multicast
       into each other's stages, so they must stay on the same tile, and one
       tile per CTA is what keeps them together. *)
    | None -> if grid_cluster k || total_tiles <= 148 then total_tiles else 148
  in
  let persistent = grid < total_tiles in
  Sass.isetp_ne_u32 b p_role r_warp alloc_warp;
  Sass.bra b p_role "INIT_DONE";
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
        Sass.syncs_exch b ~base:(mbar_reg st p.pname ~stage:s ~buf:s) ~imm:0 ~v:ur_init
      done)
    k.pipes;
  Sass.label b "ALLOC";
  Sass.umov b ur_init (ncols / 32);
  Sass.depbar_sb0 b;
  Sass.utcatomsws_fas b ur_init;
  Sass.plop3_up0 b 0;
  Sass.bra b 0 "ALLOC_OK";
  Sass.nanosleep b;
  Sass.jmp b "ALLOC";
  Sass.label b "ALLOC_OK";
  Sass.ushf_l b ur_init ur_init 5;
  Sass.mov_ur b r_tmp ur_init;
  Sass.sts_ur b ~ur:ur_smem ~imm:(slot_off - 0x400) ~data:r_tmp;
  Sass.uvirtcount_dealloc b;
  Sass.label b "INIT_DONE";
  Sass.membar_cta b;
  Sass.fence_view_async b;
  Sass.bar_sync b;
  Sass.lds b r_tmp ~ur:ur_smem ~imm:(slot_off - 0x400);
  Sass.r2ur b ur_tmem r_tmp;
  (* roles *)
  List.iter
    (function
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
        (* One pass of the tile loop covers one accumulator buffer each, so a
           barrier belonging to a buffer completes exactly once per pass, and
           its parity flips once per pass like a stage barrier. A CTA that runs
           out of tiles part way through a pass skips the rest of it. *)
        let tl = new_label st "TILES" in
        let tl_end = new_label st "TILES_END" in
        if persistent then Sass.label b tl;
        for buf = 0 to nbuf - 1 do
          if buf > 0 then begin
            Sass.isetp_lt_u32_imm b p_role r_tile (tiles_m * tiles_n);
            Sass.bra b ~neg:true p_role tl_end
          end;
          tile_indices ();
          Sass.uiadd3 b ur_acc ur_tmem (buf * acc_cols);
          List.iter (lower_stmt st ~stage:0 ~buf ~tx_done:(Hashtbl.create 1) ~tma_index:(ref 0)) body;
          Sass.iadd3_c b r_tile r_tile grid
        done;
        List.iter
          (fun p ->
            if (pipe st p).per_buffer
            then (let r = r_parity.(Hashtbl.find st.pipe_index p) in Sass.lop3_xor_imm b r r 0x80000000))
          (List.rev (waits [] body));
        if persistent then begin
          Sass.isetp_lt_u32_imm b p_role r_tile (tiles_m * tiles_n);
          Sass.bra b p_role tl
        end;
        Sass.label b tl_end;
        if lo <= alloc_warp && alloc_warp <= hi then dealloc st;
        if grid_cluster k then Sass.cluster_barrier b;
        Sass.exit b;
        Sass.label b skip
      | _ -> failwith "top level must be roles")
    k.body;
  Sass.exit b;
  let nregs = round_up (st.max_reg + 1 + 2) 8 in
  let header =
    List.map (fun l -> "# " ^ l) (String.split_on_char '\n' (Dsl2.to_string k))
    @ [ ".kernel " ^ k.name; ".sm sm_100a"; Printf.sprintf ".regs %d" nregs
      ; ".barriers 2"
      ; Printf.sprintf ".threads %d" nthreads; Printf.sprintf ".smem %d" static_bytes; Printf.sprintf ".dynsmem %d" dyn_bytes
      ; Printf.sprintf ".tile %d %d %d" k.tile_m k.tile_n k.tile_k
        (* the operand boxes a tensor map must describe: they are the shared
           tiles, which a two-CTA MMA makes narrower than the output tile *)
      ; Printf.sprintf ".box %d %d"
          (match List.find_opt (fun (t : stile) -> t.sname = "sa") k.smem with Some t -> t.srows | None -> k.tile_m)
          (match List.find_opt (fun (t : stile) -> t.sname = "sb") k.smem with Some t -> t.srows | None -> k.tile_n)
      ; Printf.sprintf ".grid %d 1" grid; Printf.sprintf ".mbarriers %d" !nslots
      ; Printf.sprintf ".cluster %d" (ctas k)
      ; (if Sys.getenv_opt "WARPC_STAGED_EPILOGUE" = None then ".cstore tma" else ".cstore direct")
      ; ".tcgen05"
      ; ".params " ^ String.concat " " (List.map (fun _ -> "8") k.params) ]
  in
  header @ Sched.schedule (Sass.items b)
