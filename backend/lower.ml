(* From a DSL kernel to the SASS instruction stream (before scheduling).

   Layouts: mma fixes them. Its shared-memory operands get the UMMA
   canonical K-major layout (core matrices of 8 rows x 16 bytes; LBO between
   K chunks, SBO between 8-row groups; no swizzle yet), its tensor-memory
   result the accumulator layout (row = lane, column = element). Every
   address a thread computes comes from composing a thread-value
   arrangement with the storage layouts of both ends of a copy and taking
   the strided form; the expression is then lowered to integer SASS. *)

open Layouts
open Dsl

let elem_bytes = function F16 -> 2 | F32 -> 4
let pow2 n = n > 0 && n land (n - 1) = 0
let rec log2 n = if n <= 1 then 0 else 1 + log2 (n / 2)
let round_up a m = (a + m - 1) / m * m

(* ---- layouts ---- *)

let lbo_bytes = 128
let sbo_bytes = 256

(* the canonical layout of a (rows x 16) f16 tile, in elements *)
let smem_layout ~rows : Linear.t =
  Group
    [ Group [ Axis { size = rows / 8; stride = sbo_bytes / 2 }; Axis { size = 8; stride = 8 } ]
    ; Group [ Axis { size = 2; stride = lbo_bytes / 2 }; Axis { size = 8; stride = 1 } ]
    ]

(* the (rows x cols) row-major tile of a matrix with leading dimension ld *)
let rowmajor ~rows ~cols ~ld : Linear.t = Group [ Axis { size = rows; stride = ld }; Axis { size = cols; stride = 1 } ]

(* ---- address expressions from the algebra ---- *)

(* The map from (iteration, thread, value) to the storage address, for a copy
   of a (rows x cols) tile by [nthreads] threads moving [v] contiguous
   elements each per iteration. Returns the strided form, or None when the
   vector is not contiguous under this storage. *)
let copy_expr ~rows ~cols ~nthreads ~v ~(storage : Linear.t) : Expr.t option =
  let total = rows * cols in
  if total mod (nthreads * v) <> 0 then None
  else begin
    let iters = total / (nthreads * v) in
    let tv : Linear.t =
      Group
        [ Group [ Axis { size = iters; stride = nthreads * v }; Axis { size = nthreads; stride = v } ]
        ; Axis { size = v; stride = 1 }
        ]
    in
    let f : (Space.thread_value, Space.logical) Layout.t = Layout.of_linear tv in
    let comp = Layout.compose f (Layout.storage storage) in
    let at it t x = Layout.offset comp (Coord.Tuple [ Tuple [ Idx it; Idx t ]; Idx x ]) in
    let contiguous =
      List.for_all
        (fun (it, t) -> List.for_all (fun x -> at it t x - at it t 0 = x) (List.init v Fun.id))
        ([ 0, 0; 0, 1; 0, nthreads - 1 ] @ if iters > 1 then [ 1, 0; iters - 1, nthreads - 1 ] else [])
    in
    if not contiguous then None
    else
      match Layout.strided_form comp with
      | None -> failwith "copy map has no strided form"
      | Some e -> Some e
  end

let v_it = "c0_0" and v_tid = "c0_1" and v_val = "c1"

(* ---- lowering state ---- *)

type st =
  { b : Sass.t
  ; k : kernel
  ; nthreads : int
  ; smem_off : (string, int) Hashtbl.t
  ; mats : (string, mat) Hashtbl.t
  ; param_index : (string, int) Hashtbl.t
  ; tmem_written : (string, unit) Hashtbl.t
  ; pipe_phase : (string, int) Hashtbl.t
  ; pipe_ur : (string, int) Hashtbl.t
  ; mutable labels : int
  ; mutable scratch : int
  ; mutable max_reg : int
  ; smem_bytes : int
  ; slot_off : int
  ; ncols : int
  }

(* fixed registers *)
let r_tid = 0 and r_warp = 2 and r_lane = 3 and r_tmp = 4 and r_tmp2 = 6
let scratch_lo = 8 and scratch_hi = 72
let r_ldtm = 72

(* fixed uniform registers *)
let ur_desc = 4 and ur_param i = 8 + (2 * i)
let ur_cta = 14 and ur_tmp = 15 and ur_smem = 16 and ur_tmem = 17 and ur_tmem_warp = 18
let ur_init = 20 and ur_pipe i = 22 + i and ur_alloc = 24
let ur_da = 30 and ur_db = 32 and ur_zero = 34 and ur_idesc = 35 (* URe even, URh = URe + 1: a vendor table rule *)

let fresh st =
  let r = st.scratch in
  if r >= scratch_hi then failwith "out of scratch registers";
  st.scratch <- r + 1;
  st.max_reg <- max st.max_reg r;
  r

let fresh2 st =
  st.scratch <- round_up st.scratch 2;
  let r = st.scratch in
  if r + 1 >= scratch_hi then failwith "out of scratch registers";
  st.scratch <- r + 2;
  st.max_reg <- max st.max_reg (r + 1);
  r

let fresh4 st =
  st.scratch <- round_up st.scratch 4;
  let r = st.scratch in
  if r + 3 >= scratch_hi then failwith "out of scratch registers";
  st.scratch <- r + 4;
  st.max_reg <- max st.max_reg (r + 3);
  r

let new_label st prefix =
  st.labels <- st.labels + 1;
  Printf.sprintf "%s_%d" prefix st.labels

(* ---- Expr -> SASS: the register holding the value ---- *)

let rec lower_expr st (env : string -> int) (e : Expr.t) : int =
  let b = st.b in
  match e with
  | Const c ->
    let r = fresh st in
    Sass.mov_imm b r c;
    r
  | Var v -> env v
  | Sum (terms, k) ->
    let acc =
      List.fold_left
        (fun acc (coef, t) ->
          let rt = lower_expr st env t in
          match acc with
          | None when coef = 1 -> Some rt
          | None ->
            let r = fresh st in
            Sass.imad_rz b r rt coef;
            Some r
          | Some a ->
            let r = fresh st in
            Sass.imad b r rt coef a;
            Some r)
        None
        terms
    in
    (match acc, k with
     | None, k ->
       let r = fresh st in
       Sass.mov_imm b r k;
       r
     | Some a, 0 -> a
     | Some a, k ->
       let r = fresh st in
       Sass.iadd3_c b r a k;
       r)
  | Div (t, w) ->
    if not (pow2 w) then failwith "division by a non-power of two";
    let rt = lower_expr st env t in
    let r = fresh st in
    Sass.shf_r b r rt (log2 w);
    r
  | Mod (t, m) ->
    if not (pow2 m) then failwith "modulus by a non-power of two";
    let rt = lower_expr st env t in
    let r = fresh st in
    Sass.lop3_and b r rt (m - 1);
    r
  | Xor (t1, t2) ->
    let r1 = lower_expr st env t1 in
    let r2 = lower_expr st env t2 in
    let r = fresh st in
    Sass.lop3_xor b r r1 r2;
    r
  | Let (x, e1, body) ->
    let r1 = lower_expr st env e1 in
    lower_expr st (fun v -> if v = x then r1 else env v) body

(* ---- statements ---- *)

let mat st name = try Hashtbl.find st.mats name with Not_found -> failwith ("unknown tile " ^ name)
let is_param st name = Hashtbl.mem st.param_index name
let is_smem st name = Hashtbl.mem st.smem_off name
let is_tmem st name = List.exists (fun (m : mat) -> m.name = name) st.k.tmem

(* 64-bit global address = param base + 32-bit byte offset register *)
let global_addr st ~param ~off =
  let lo = fresh2 st in
  Sass.iadd3_ur st.b lo ~carry:0 off (ur_param param);
  Sass.imad_x_ur st.b (lo + 1) (ur_param param + 1) 0;
  lo

let lower_copy_to_smem st ~(dst : ref_) ~(src : ref_) (env : string -> int) =
  let d = mat st dst.tile and s = mat st src.tile in
  if d.rows <> s.rows || d.cols <> 16 || d.dtype <> F16 then failwith "copy to smem: tile shapes";
  let kk = match src.ktile with Some v -> env v | None -> 0 in
  let bytes = elem_bytes F16 in
  let rows = d.rows in
  let src_storage = rowmajor ~rows ~cols:16 ~ld:s.cols in
  let dst_storage = smem_layout ~rows in
  let rec pick = function
    | [] -> failwith "copy: no vector width fits both layouts"
    | v :: rest ->
      (match copy_expr ~rows ~cols:16 ~nthreads:st.nthreads ~v ~storage:src_storage,
             copy_expr ~rows ~cols:16 ~nthreads:st.nthreads ~v ~storage:dst_storage with
       | Some es, Some ed -> v, es, ed
       | _ -> pick rest)
  in
  let v, es, ed = pick [ 8; 4; 2; 1 ] in
  let width = v * 8 * bytes in
  let iters = rows * 16 / (st.nthreads * v) in
  let tid_env x = if x = v_tid then r_tid else failwith ("unbound " ^ x) in
  for it = 0 to iters - 1 do
    let fix e =
      Expr.subst e (fun x -> if x = v_it then Some it else if x = v_val then Some 0 else None)
    in
    let e_src = Expr.add (Expr.scale bytes (fix es)) (Expr.Const (bytes * 16 * kk)) in
    let e_dst = Expr.scale bytes (fix ed) in
    let r_goff = lower_expr st tid_env e_src in
    let addr = global_addr st ~param:(Hashtbl.find st.param_index s.name) ~off:r_goff in
    let data = fresh4 st in
    Sass.ldg_w st.b ~width data ~base:addr ~imm:0;
    let r_soff = lower_expr st tid_env e_dst in
    Sass.sts st.b ~width ~r:r_soff ~ur:ur_smem ~imm:(Hashtbl.find st.smem_off d.name) ~data
  done

let lower_copy_from_tmem st ~(dst : ref_) ~(src : ref_) =
  let d = mat st dst.tile and s = mat st src.tile in
  if dst.rows <> Rows_of_warp || src.rows <> Rows_of_warp then failwith "tmem copy: rows of warp only";
  if d.rows <> s.rows || d.cols <> s.cols || d.dtype <> F32 then failwith "tmem copy: shapes";
  if d.rows <> st.nthreads then failwith "tmem copy: the warps must cover the rows (M = 32 * warps)";
  let n = d.cols in
  if not (pow2 n && n >= 32 && n <= 128) then failwith "tmem copy: N must be 32, 64 or 128";
  (* the tensor-memory read: thread t of warp w gets row 32 w + t, all n columns *)
  Sass.lea_ur st.b r_tmp2 r_warp ur_tmem 0x15;
  Sass.r2ur st.b ur_tmem_warp r_tmp2;
  Sass.ldtm st.b r_ldtm ~n ~addr:ur_tmem_warp;
  st.max_reg <- max st.max_reg (r_ldtm + n - 1);
  (* the store: the thread-value map (row = tid, value = column) composed with C's storage *)
  let storage = rowmajor ~rows:d.rows ~cols:n ~ld:d.cols in
  let tv : Linear.t = Group [ Axis { size = st.nthreads; stride = n }; Axis { size = n; stride = 1 } ] in
  let comp = Layout.compose (Layout.of_linear tv : (Space.thread_value, Space.logical) Layout.t) (Layout.storage storage) in
  let e = match Layout.strided_form comp with Some e -> e | None -> failwith "epilogue map" in
  let at t x = Layout.offset comp (Coord.Tuple [ Idx t; Idx x ]) in
  if not (List.for_all (fun x -> at 5 x - at 5 0 = x) (List.init n Fun.id)) then failwith "epilogue: columns not contiguous";
  let e0 = Expr.scale 4 (Expr.subst e (fun x -> if x = "c1" then Some 0 else None)) in
  let r_off = lower_expr st (fun x -> if x = "c0" then r_tid else failwith ("unbound " ^ x)) e0 in
  let addr = global_addr st ~param:(Hashtbl.find st.param_index d.name) ~off:r_off in
  for q = 0 to (n / 4) - 1 do
    Sass.stg128 st.b ~base:addr ~imm:(16 * q) ~data:(r_ldtm + (4 * q))
  done

let smem_descriptor st ~ur ~tile =
  let b = st.b in
  Sass.uiadd3 b ur ur_smem (Hashtbl.find st.smem_off tile);
  Sass.ushf_r b ur ur 4;
  Sass.ulop3_and b ur ur 0x3fff;
  Sass.ulop3_or b ur ur ((lbo_bytes lsr 4) lsl 16);
  Sass.umov b (ur + 1) ((sbo_bytes lsr 4) lor (1 lsl 14))

let lower_mma st ~d ~a ~bb =
  let ma = mat st a and mb = mat st bb and md = mat st d in
  if not (is_smem st a && is_smem st bb && is_tmem st d) then failwith "mma: operands in smem, result in tmem";
  if ma.cols <> 16 || mb.cols <> 16 || ma.dtype <> F16 || mb.dtype <> F16 then failwith "mma: f16 K=16 tiles";
  if md.rows <> ma.rows || md.cols <> mb.rows then failwith "mma: shapes";
  let m = md.rows and n = md.cols in
  if m <> 128 then failwith "mma: M = 128 only for now";
  smem_descriptor st ~ur:ur_da ~tile:a;
  smem_descriptor st ~ur:ur_db ~tile:bb;
  Sass.umov st.b ur_idesc ((1 lsl 4) lor ((n lsr 3) lsl 17) lor ((m lsr 4) lsl 24));
  Sass.umov st.b ur_zero 0;
  let acc = Hashtbl.mem st.tmem_written d in
  Hashtbl.replace st.tmem_written d ();
  Sass.utchmma st.b ~a:ur_da ~bb:ur_db ~d:ur_tmem ~e:ur_zero ~idesc:ur_idesc ~acc

let lower_wait st p =
  let phase = try Hashtbl.find st.pipe_phase p with Not_found -> 0 in
  Hashtbl.replace st.pipe_phase p (phase + 1);
  let parity = phase mod 2 in
  (* the odd phase is selected by bit 31 of the register operand, as ptxas spells it *)
  let parity_reg = if parity = 0 then None else (Sass.mov_imm st.b r_tmp 0x80000000; Some r_tmp) in
  let l = new_label st "WAIT" in
  Sass.label st.b l;
  Sass.syncs_trywait st.b 0 ~base:(Hashtbl.find st.pipe_ur p) ~imm:0 ~parity_reg;
  Sass.bra st.b ~neg:true 0 l

let rec lower_stmt st (env : string -> int) = function
  | Copy (dst, src) ->
    st.scratch <- scratch_lo;
    if is_smem st dst.tile && is_param st src.tile then lower_copy_to_smem st ~dst ~src env
    else if is_param st dst.tile && is_tmem st src.tile then lower_copy_from_tmem st ~dst ~src
    else failwith "copy: only global -> smem and tmem -> global for now"
  | Mma { d; a; b } -> lower_mma st ~d ~a ~bb:b
  | Commit p -> Sass.utcbar st.b ~mbar:(Hashtbl.find st.pipe_ur p)
  | Wait p -> lower_wait st p
  | Fence_barrier ->
    Sass.membar_cta st.b;
    Sass.fence_view_async st.b;
    Sass.bar_sync st.b
  | For (v, count, body) ->
    for i = 0 to count - 1 do
      List.iter (lower_stmt st (fun x -> if x = v then i else env x)) body
    done
  | Warp (w, body) ->
    let l = new_label st "SKIP" in
    Sass.isetp_ne_u32 st.b 1 r_warp w;
    Sass.bra st.b 1 l;
    List.iter (lower_stmt st env) body;
    Sass.label st.b l

(* ---- the kernel ---- *)

let lower (k : kernel) : string list =
  let b = Sass.create () in
  let nthreads = 32 * k.nwarps in
  let mats = Hashtbl.create 8 in
  List.iter (fun (m : mat) -> Hashtbl.replace mats m.name m) (k.params @ k.smem @ k.tmem);
  let param_index = Hashtbl.create 4 in
  List.iteri (fun i (m : mat) -> Hashtbl.replace param_index m.name i) k.params;
  (* shared memory: tiles at 1024-byte alignment, then one mbarrier per pipe, then the TMEM slot *)
  let smem_off = Hashtbl.create 4 in
  let off = ref 0 in
  List.iter
    (fun (m : mat) ->
      Hashtbl.replace smem_off m.name !off;
      off := round_up (!off + (m.rows * m.cols * elem_bytes m.dtype)) 1024)
    k.smem;
  let pipe_off = List.mapi (fun i p -> p, !off + (8 * i)) k.pipes in
  off := !off + (8 * List.length k.pipes);
  let slot_off = !off in
  let smem_bytes = slot_off + 4 in
  let ncols =
    match k.tmem with
    | [ m ] -> if m.dtype <> F32 then failwith "tmem tile must be f32" else max 32 m.cols
    | _ -> failwith "exactly one tmem tile for now"
  in
  if not (pow2 ncols) then failwith "tmem columns must be a power of two";
  let st =
    { b; k; nthreads; smem_off; mats; param_index; tmem_written = Hashtbl.create 2; pipe_phase = Hashtbl.create 2
    ; pipe_ur = Hashtbl.create 2; labels = 0; scratch = scratch_lo; max_reg = r_ldtm; smem_bytes; slot_off; ncols }
  in
  List.iteri (fun i (p, _) -> Hashtbl.replace st.pipe_ur p (ur_pipe i)) pipe_off;
  (* prologue *)
  Sass.ldc b 1 0x37c;
  Sass.s2r_tid b r_tid;
  Sass.ldcu64 b ur_desc 0x358;
  List.iteri (fun i _ -> Sass.ldcu64 b (ur_param i) (0x380 + (8 * i))) k.params;
  Sass.s2ur_cta b ur_cta;
  Sass.umov b ur_tmp 0x400;
  Sass.ulea b ur_smem ur_cta ur_tmp 0x18;
  Sass.shf_r b r_warp r_tid 5;
  Sass.lop3_and b r_lane r_tid 31;
  List.iter (fun (p, o) -> Sass.uiadd3 b (Hashtbl.find st.pipe_ur p) ur_smem o) pipe_off;
  (* warp 0: mbarrier init (count 1) per pipe, TMEM allocation *)
  Sass.isetp_ne_u32 b 1 r_warp 0;
  Sass.bra b 1 "INIT_DONE";
  Sass.umov b ur_init 1;
  Sass.uiadd3_neg b ur_init ur_init 0x100000;
  Sass.ushf_l b (ur_init + 1) ur_init 0xb;
  Sass.ushf_l b ur_init ur_init 0x1;
  List.iter (fun (p, _) -> Sass.syncs_exch b ~base:(Hashtbl.find st.pipe_ur p) ~imm:0 ~v:ur_init) pipe_off;
  Sass.label b "ALLOC";
  Sass.umov b ur_alloc (ncols / 32);
  Sass.depbar_sb0 b;
  Sass.utcatomsws_fas b ur_alloc;
  Sass.plop3_up0 b 0;
  Sass.bra b 0 "ALLOC_OK";
  Sass.nanosleep b;
  Sass.jmp b "ALLOC";
  Sass.label b "ALLOC_OK";
  (* the allocation returns a slot in units of 32 columns; the address is slot << 5 *)
  Sass.ushf_l b ur_alloc ur_alloc 5;
  Sass.mov_ur b r_tmp ur_alloc;
  Sass.sts_ur b ~ur:ur_smem ~imm:slot_off ~data:r_tmp;
  Sass.uvirtcount_dealloc b;
  Sass.label b "INIT_DONE";
  (* the slot store must be performed before the other warps read it *)
  Sass.membar_cta b;
  Sass.fence_view_async b;
  Sass.bar_sync b;
  Sass.lds b r_tmp ~ur:ur_smem ~imm:slot_off;
  Sass.r2ur b ur_tmem r_tmp;
  (* body *)
  List.iter (lower_stmt st (fun x -> failwith ("unbound loop variable " ^ x))) k.body;
  (* epilogue: everyone done with tensor memory, then warp 0 frees it *)
  Sass.bar_sync b;
  Sass.isetp_ne_u32 b 1 r_warp 0;
  Sass.bra b 1 "EXIT";
  (* mask = ((2^(ncols/32) - 1) << slot) | (1 << (slot + 16)), slot = column / 32 *)
  Sass.ulop3_and b ur_alloc ur_tmem 0xffff;
  Sass.ushf_r b ur_alloc ur_alloc 5;
  Sass.umov b (ur_alloc + 1) ((1 lsl (ncols / 32)) - 1);
  Sass.ushf_l_ur b (ur_alloc + 1) (ur_alloc + 1) ur_alloc;
  Sass.uiadd3 b (ur_alloc + 2) ur_alloc 16;
  Sass.umov b (ur_alloc + 3) 1;
  Sass.ushf_l_ur b (ur_alloc + 3) (ur_alloc + 3) (ur_alloc + 2);
  Sass.ulop3_or_ur b (ur_alloc + 1) (ur_alloc + 1) (ur_alloc + 3);
  Sass.ulop3_not b (ur_alloc + 1) (ur_alloc + 1);
  Sass.utcatomsws_and b (ur_alloc + 1);
  Sass.label b "EXIT";
  Sass.exit b;
  let nregs = round_up (st.max_reg + 1 + 2) 8 in
  if nregs > 255 then failwith "register budget exceeded";
  let header =
    List.map (fun l -> "# " ^ l) (String.split_on_char '\n' (Dsl.to_string k))
    @ [ ".kernel " ^ k.name; ".sm sm_100a"; Printf.sprintf ".regs %d" nregs; ".barriers 1"
      ; Printf.sprintf ".threads %d" nthreads; Printf.sprintf ".smem %d" smem_bytes; ".tcgen05"
      ; ".params " ^ String.concat " " (List.map (fun _ -> "8") k.params) ]
  in
  header @ Sched.schedule (Sass.items b)
