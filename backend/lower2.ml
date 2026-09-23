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
let elem_bytes = function F16 -> 2 | F32 -> 4

(* registers *)
let r_tid = 0 and r_warp = 2 and r_lane = 3 and r_tmp = 4 and r_cnt = 8 and r_tmp2 = 9
let r_tilen = 12 and r_tilem = 13 and r_tile = 14 and r_stage = 144 and r_swz = 216

(* registers an emission site may use for its intermediate values; dead once
   the site's results have been read *)
let scratch = List.init 64 (fun i -> 152 + i)
let r_parity = [| 5; 6; 7; 15 |] (* one parity register per pipe, by declaration order *)
let r_data = [| 16; 80 |] (* two 64-register epilogue buffers *)
let p_role = 1 and p_lane0 = 2 and p_loop = 3 and p_lead = 4

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
  }

let new_label st p = st.labels <- st.labels + 1; Printf.sprintf "%s_%d" p st.labels

(* One MMA covers the accumulators of a CTA pair: the leader issues it, and
   each CTA holds half of each operand. *)
let two_cta st =
  if st.k.pair && st.k.cluster <> 2 then failwith "a two-CTA MMA needs a cluster of 2 along M";
  st.k.pair

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
  let by_mma = reads (function Mma { a; b; _ } -> a = t.sname || b = t.sname | _ -> false) k.body in
  let by_store = reads (function Store { via; _ } -> via = t.sname | _ -> false) k.body in
  let filled = reads (function Tma { dst; _ } -> dst = t.sname | _ -> false) k.body in
  (match by_mma, by_store with
   | true, false -> ignore (Atom.umma_kmajor l ~elem ~mma_k:16)
   | false, true -> ignore (Atom.tma_box l ~elem)
   | false, false -> failwith (t.sname ^ ": no instruction reads this tile, so nothing fixes its layout")
   | true, true -> failwith (t.sname ^ ": read both by an MMA and by a store"));
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
  Atom.umma_kmajor (Hashtbl.find st.layouts name) ~elem:(elem_bytes t.sdtype) ~mma_k:16

let lower_wait st p ~stage ~buf =
  let pp = pipe st p in
  let r = r_parity.(Hashtbl.find st.pipe_index p) in
  let l = new_label st "WAIT" in
  Sass.label st.b l;
  Sass.syncs_trywait st.b 0 ~base:(mbar_reg st p ~stage ~buf) ~imm:0 ~parity_reg:(Some r);
  Sass.bra st.b ~neg:true 0 l;

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

let release_to_pair st p ~stage ~buf =
  Sass.syncs_arrive st.b ~guard:p_lane0 ~base:(mbar_reg st p ~stage ~buf) ~imm:0;
  if two_cta st && not (pipe st p).cross
  then begin
    Sass.uiadd3 st.b ur_peer_bar ur_peer (8 * mbar_slot st p ~stage ~buf);
    Sass.syncs_arrive_red st.b ~guard:p_lane0 ~base:ur_peer_bar ~imm:0
  end

(* Everything a store needs, derived and checked, with nothing emitted: the
   layouts it composes, the expressions it will emit, the immediates. *)
type store_plan =
  { sp_dst : string
  ; e_ld : Expr.t
  ; imm_ld : int array
  ; e_copy : Expr.t
  ; e_y : Expr.t
  ; imm_y : int array
  ; x0 : int
  ; imm_x : int array
  ; sts : (Space.thread_value, Space.physical) Layout.t
  ; sp_n : int
  ; vec : int
  ; sp_elem : int
  ; copy : int
  ; copies : int
  ; blocks_n : int
  }

let store_plan st ~dst ~src ~via =
    let acc = ttile st src and sc = stile st via in
    let box = Hashtbl.find st.layouts via in
    let copies =
      match sc.ring with Per_warp n -> n | Stages -> failwith (via ^ ": a staging tile has copies per warp")
    in
    let copy = Hashtbl.find st.copy_bytes via in
    let n = sc.scols and elem = elem_bytes sc.sdtype in
    if sc.srows <> Atom.ldtm_block then failwith (via ^ ": a warp's block has the 32 rows of its lane quarter");
    let blocks_m = acc.trows / Atom.ldtm_block and blocks_n = acc.tcols / n in
    (* The tensor-memory load's fragment, dealt over the accumulator's blocks
       and composed with the accumulator's layout, is the load's address map;
       Atom checks it against what one warp-uniform address reads. *)
    let frag = Atom.ldtm_32x32b ~n in
    let block = Shape.Product [ Bound Atom.ldtm_block; Bound n ] in
    let grid = Linear.canonical (Product [ Bound blocks_m; Bound blocks_n ]) in
    let ld =
      Layout.compose
        (Layout.interleave ~by:grid frag)
        (Layout.divide ~by:block (Atom.tmem_accumulator ~rows:acc.trows ~cols:acc.tcols))
    in
    Atom.check_ldtm ld ~blocks_m ~blocks_n ~n;
    let rt = Shape.Bound blocks_m in
    let w_of = function Coord.Idx w -> w | Tuple _ -> assert false in
    let e_ld, imm_ld =
      split ~name:"tensor-memory load" ~rt ~n:blocks_n (fun c ch ->
        Layout.offset ld (Coord.Tuple [ Tuple [ Idx (w_of c); Idx ch ]; Tuple [ Idx 0; Idx 0 ] ]))
    in
    (* The staging write is the same fragment composed with the staging tile's
       layout -- the box the copy engine reads -- so a register's address is
       where the store will look for it. *)
    let sts = Layout.compose frag box in
    if not (Layout.is_injective sts) then failwith (via ^ ": two values of a fragment land on one address");
    let vec = 16 / elem in
    for l = 0 to Atom.ldtm_block - 1 do
      for q = 0 to (n / vec) - 1 do
        let a e = Layout.offset sts (Coord.Tuple [ Idx l; Idx ((vec * q) + e) ]) in
        if a 0 mod 16 <> 0 then failwith "store: a register vector is not 16-byte aligned";
        for e = 1 to vec - 1 do
          if a e <> a 0 + (e * elem) then failwith "store: a register vector is not contiguous"
        done
      done
    done;
    (* A block's place in the output is its place in the tile's division into
       blocks; the copy engine takes it as a coordinate pair. *)
    let tile : (Space.logical, Space.logical) Layout.t =
      Layout.divide ~by:block (Layout.of_linear (Linear.canonical (Product [ Bound acc.trows; Bound acc.tcols ])))
    in
    let origin c ch = Layout.offset tile (Coord.Tuple [ Tuple [ Idx 0; Idx 0 ]; Tuple [ Idx (w_of c); Idx ch ] ]) in
    let e_y, imm_y = split ~name:"store row" ~rt ~n:blocks_n (fun c ch -> origin c ch / acc.tcols) in
    let e_x, imm_x = split ~name:"store column" ~rt ~n:blocks_n (fun c ch -> origin c ch mod acc.tcols) in
    let x0 = match e_x with Expr.Const k -> k | _ -> failwith "store: a block's column depends on the warp" in
    (* the warp's copies of the staging tile: the copies of the block row it
       reads *)
    let e_copy = Expr.scale (copies * copy) (Expr.var "c") in
    (* The runtime coordinate of all of these is the block row, which the load
       fixes to the warp's lane quarter. *)
    { sp_dst = dst; e_ld; imm_ld; e_copy; e_y; imm_y; x0; imm_x; sts; sp_n = n; vec; sp_elem = elem; copy; copies
    ; blocks_n }

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
  Emit.into em ~range ~reg (quarter p.e_y) ~dst:r_tmp;
  Sass.lea_ur b r_tmp r_tmp ur_tile_m 0;
  Sass.r2ur b ur_ey r_tmp;
  st.max_reg <- max st.max_reg em.high;
  let imm_ld = p.imm_ld and imm_x = p.imm_x and imm_y = p.imm_y and x0 = p.x0 and blocks_n = p.blocks_n in
  let dst = p.sp_dst in
    for ch = 0 to blocks_n - 1 do
      let d = r_data.(ch mod 2) and slot = ch mod copies in
      Sass.ldtm_off b d ~n ~addr:ur_epi ~imm:imm_ld.(ch);
      st.max_reg <- max st.max_reg (d + n - 1);
      (* The copy this block goes into was last read by the store [copies]
         blocks back -- in this tile or the previous one. Stores finish in
         order, so at most [copies - 1] may still be reading when it is
         rewritten: the rest keep going while this block is staged. *)
      Sass.depbar_le b ~n:(copies - 1);
      for q = 0 to (n / vec) - 1 do
        Sass.sts_r b ~width:(8 * vec * elem) ~r:(r_swz + q) ~imm:(slot * copy) ~data:(d + (vec * q))
      done;
      (* the stores have taken the last block's values, so the load that
         produced them has landed: the accumulator is free for the next tile's
         MMAs while its last blocks are still being written out *)
      if ch = blocks_n - 1 then (match release with Some p -> release_to_pair st p ~stage:0 ~buf | None -> ());
      (* The copy engine reads the staging copy, so the writes into it must
         have landed, not merely issued: a read scoreboard only says the store
         has taken its data out of the registers. The fence publishes them to
         the async proxy and the wait comes after it -- waiting first leaves
         the youngest stores unpublished and the engine reads the sixteen bytes
         they were about to overwrite. *)
      Sass.fence_view_async b;
      Sass.warpsync b;
      Sass.uiadd3 b ur_st ur_esrc (slot * copy);
      Sass.uiadd3 b (ur_st + 1) ur_tile_n (x0 + imm_x.(ch));
      Sass.uiadd3 b (ur_st + 2) ur_ey imm_y.(ch);
      Sass.utmastg b ~g:ur_st ~map:(ur_param (param_index st dst));
      Sass.utmacmdflush b
    done

let rec lower_stmt st ~stage ~buf ~(tx_done : (string, unit) Hashtbl.t) ~(tma_index : int ref) = function
  | Wait p -> lower_wait st p ~stage ~buf
  | Tma { dst; src; rows; pipe = p } ->
    let b = st.b in
    (* A two-CTA MMA reads both CTAs' stages, so the stage is full only when
       both halves have landed. Every load of the pair reports to the LEADER's
       copy of the barrier -- the CTA field of its address with the pair bit
       cleared, as CUTLASS masks it (0xfefffff8) -- and the leader alone states
       the bytes to expect, the pair's whole stage. *)
    let bar_of p = if two_cta st then `Lead (8 * mbar_slot st p ~stage ~buf) else `Own (mbar_reg st p ~stage ~buf) in
    if not (Hashtbl.mem tx_done p) then begin
      Hashtbl.replace tx_done p ();
      if two_cta st
      then begin
        let l = new_label st "NOT_LEADER" in
        Sass.bra b ~neg:true p_lead l;
        Sass.syncs_arrive_tx b ~guard:p_lane0 ~base:(mbar_reg st p ~stage ~buf) ~imm:0 ~tx:r_tmp2;
        Sass.label b l
      end
      else Sass.syncs_arrive_tx b ~guard:p_lane0 ~base:(mbar_reg st p ~stage ~buf) ~imm:0 ~tx:r_tmp2
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
    (* the next stage's box starts where this one's K extent ends *)
    Sass.uiadd3 b (g + 2) (g + 2) (snd (Atom.dims (Hashtbl.find st.layouts dst)))
  | Mma { d = _; a; b = bb } ->
    let b = st.b in
    let da = operand_desc st a and db = operand_desc st bb in
    (* one MMA consumes 16 of the stage's K columns; the stage's K extent is
       its layout's *)
    let k_of name = snd (Atom.dims (Hashtbl.find st.layouts name)) in
    if k_of a <> k_of bb then failwith "mma: the operands' stages hold different K extents";
    let steps = k_of a / 16 in
    (* only the very first MMA of the kernel overwrites the accumulator; that
       one reads a flag the loop body sets, every other one accumulates *)
    let kept = st.k.depth <= 4 in
    let base_a = if kept then ur_dbase_block + (2 * stage) else ur_dbase in
    let base_b = base_a + 1 in
    if not kept
    then begin
      desc_low st ~ur:base_a ~off:(Hashtbl.find st.smem_dyn a + (stage * st.stage_bytes));
      desc_low st ~ur:base_b ~off:(Hashtbl.find st.smem_dyn bb + (stage * st.stage_bytes))
    end;
    for j = 0 to steps - 1 do
      Sass.uiadd3 b ur_da base_a (da.kstep * j);
      Sass.uiadd3 b ur_db base_b (db.kstep * j);
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
    done
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
  | Store { dst; src; via; release } -> store_body st (store_plan st ~dst ~src ~via) ~release ~buf
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
     | Some (Mma { a; b = bb; _ }) ->
       Sass.umov b ur_mma_count 0;
       Sass.umov b ur_zero 0;
       (* the instruction descriptor states the MMA's shape: M rows over
          the pair for a two-CTA MMA, N the accumulator's columns *)
       let acc = List.hd st.k.tmem in
       let m_rows = acc.trows * (if two_cta st then 2 else 1) and n_cols = acc.tcols in
       Sass.umov b ur_idesc ((1 lsl 4) lor ((n_cols lsr 3) lsl 17) lor ((m_rows lsr 4) lsl 24));
       Sass.umov b (ur_da + 1) (Atom.desc_high (operand_desc st a));
       Sass.umov b (ur_db + 1) (Atom.desc_high (operand_desc st bb));
       if s <= 4
       then
         for stage = 0 to s - 1 do
           desc_low st ~ur:(ur_dbase_block + (2 * stage)) ~off:(Hashtbl.find st.smem_dyn a + (stage * st.stage_bytes));
           desc_low st ~ur:(ur_dbase_block + (2 * stage) + 1) ~off:(Hashtbl.find st.smem_dyn bb + (stage * st.stage_bytes))
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
  for buf = 0 to acc.bufs - 1 do
    buffer_base st ~buf ~into:ur_acc;
    free_tmem st.b ~base:ur_acc ~ncols:acc.tcols
  done

(* A probe of the allocator alone: warp 0 allocates [ncols] columns, gives up
   its permit, frees them and exits -- the GEMM's instructions and nothing
   else, so a launch that follows shows whether the free left anything. *)
let tmem_probe ~ncols ~times =
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
  for i = 0 to times - 1 do
    free_tmem b ~base:keep.(i) ~ncols
  done;
  Sass.label b "DONE";
  Sass.exit b;
  [ Printf.sprintf ".kernel talloc_%dx%d" times ncols; ".sm sm_100a"; ".regs 16"; ".barriers 1"; ".threads 128"
  ; ".smem 1024"; ".mbarriers 1"; ".tcgen05"; ".params 8" ]
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
  if !nslots > 20 then failwith "too many mbarriers for the uniform register map";
  let slot_off = 0x400 + (8 * !nslots) in
  let static_bytes = 0x400 in
  if slot_off + (4 * nbuf) > 0x400 + static_bytes then failwith "static shared memory overflow";
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
  let acc_cols = (List.hd k.tmem).tcols in
  if not (pow2 acc_cols && acc_cols >= 32 && acc_cols * nbuf <= 512) then failwith "tmem columns";
  let st =
    { b; k; pipe_slot; pipe_index; smem_dyn; stage_bytes; slot_off; labels = 0; max_reg = r_data.(1) + 63; mma_seen = 0
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
  (* The tile a CTA owns. The map from a CTA index to a tile is a layout: the
     index's digits -- the CTA's rank in its cluster, its place in a group of
     rows, the column, the group -- name the tile, so consecutive CTAs walk
     down [group] rows before moving across and the tiles in flight share
     their operand rows in L2. What is emitted is the decided strided form of
     the map from the index to each coordinate of the tile's origin. *)
  let tiles_m = k.tile_m_count / k.cluster and tiles_n = k.tile_n_count / k.cluster_n in
  let group =
    let rec g n = if n * 2 <= tiles_m && n < 8 then g (n * 2) else n in
    let g = g 1 in
    if pow2 tiles_n && tiles_m mod g = 0 then g else 1
  in
  let width = tiles_n * k.cluster_n in
  let cta_grid : (Space.thread_value, Space.logical) Layout.t =
    Layout.of_linear
      (Group
         [ Axis { size = tiles_m / group; stride = group * k.cluster * width }
         ; Axis { size = tiles_n; stride = k.cluster_n }
         ; Axis { size = group; stride = k.cluster * width }
         ; Axis { size = k.cluster_n; stride = 1 }
         ; Axis { size = k.cluster; stride = width }
         ])
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
  (* Persistent when there are more tiles than multiprocessors: each CTA walks
     the tiles a grid apart. A cluster walks them together -- its CTAs are
     consecutive and the grid is a multiple of the cluster, so they reach the
     same cluster tile at every step -- and the stage and accumulator
     handshakes span the tile boundaries, so a CTA can be a tile ahead of its
     partner only as far as the ring lets it. *)
  let grid = if total_tiles <= Dsl2.sms then total_tiles else Dsl2.sms / ctas k * ctas k in
  let persistent = grid < total_tiles in
  (* A k loop whose tiles the ring does not divide ends part way round it,
     with the stages it used one phase ahead of the rest; the next tile would
     start at stage 0 regardless. Carrying the ring position across tiles is
     not done yet, so a persistent kernel refuses that case rather than emit
     a kernel that waits on the wrong phase. *)
  if persistent && k.k_total / k.tile_k mod k.depth <> 0
  then
    failwith
      (Printf.sprintf "ring depth %d does not divide the %d k tiles of a persistent kernel" k.depth
         (k.k_total / k.tile_k));
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
        Sass.syncs_exch b ~base:(mbar_reg st p.pname ~stage:s ~buf:s) ~imm:0 ~v:ur_init
      done)
    k.pipes;
  for buf = 0 to nbuf - 1 do
    alloc_tmem ~tag:(string_of_int buf) b ~ncols:acc_cols;
    Sass.mov_ur b r_tmp ur_init;
    Sass.sts_ur b ~ur:ur_smem ~imm:(slot_off - 0x400 + (4 * buf)) ~data:r_tmp
  done;
  Sass.uvirtcount_dealloc b;
  Sass.label b "INIT_DONE";
  Sass.membar_cta b;
  Sass.fence_view_async b;
  Sass.bar_sync b;
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
        (* a store's tile-invariant addresses, once, before the first tile *)
        let rec stores acc = function
          | Store { dst; src; via; _ } -> (dst, src, via) :: acc
          | Kloop b | Role (_, b) -> List.fold_left stores acc b
          | _ -> acc
        in
        List.iter (fun (dst, src, via) -> store_setup st (store_plan st ~dst ~src ~via)) (List.fold_left stores [] body);
        let tl = new_label st "TILES" in
        let tl_end = new_label st "TILES_END" in
        (* In a pair, the MMA and every stage barrier it waits on are the
           leader's. The other CTA's tensor-core warp has nothing to issue and
           nothing that completes for it to wait on, so it goes straight to the
           end of its role -- where it still meets the warps that use tensor
           memory and frees its own. *)
        if two_cta st && reads (function Mma _ -> true | _ -> false) body then Sass.bra b ~neg:true p_lead tl_end;
        if persistent then Sass.label b tl;
        for buf = 0 to nbuf - 1 do
          if buf > 0 then begin
            Sass.isetp_lt_u32_imm b p_role r_tile total_tiles;
            Sass.bra b ~neg:true p_role tl_end
          end;
          tile_indices ();
          buffer_base st ~buf ~into:ur_acc;
          List.iter (lower_stmt st ~stage:0 ~buf ~tx_done:(Hashtbl.create 1) ~tma_index:(ref 0)) body;
          Sass.iadd3_c b r_tile r_tile grid
        done;
        List.iter
          (fun p ->
            if (pipe st p).per_buffer
            then (let r = r_parity.(Hashtbl.find st.pipe_index p) in Sass.lop3_xor_imm b r r 0x80000000))
          (List.rev (waits [] body));
        if persistent then begin
          Sass.isetp_lt_u32_imm b p_role r_tile total_tiles;
          Sass.bra b p_role tl
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
        if uses_tmem body then Sass.bar_sync_n b ~bar:1 ~count:(32 * tmem_warps);
        if lo <= alloc_warp && alloc_warp <= hi then dealloc st;
        if grid_cluster k then Sass.cluster_barrier b;
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
      ; ".params " ^ String.concat " " (List.map (fun _ -> "8") k.params) ]
  in
  header @ Sched.schedule (Sass.items b)
