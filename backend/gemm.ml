(* One warp computes C[M x N] (f32, row-major) = A[M x K] (f16, row-major)
   . B[K x N] (f16, given transposed as Bt[N x K], row-major), with
   HMMA.16816.F32 and a K loop over global memory.

   The addresses come from the algebra: for each operand, the storage map
   is divided into atom tiles, the atom's thread-value map is interleaved
   over the tile grid, the two are composed, and the strided form of the
   composite is an affine expression in (tile, lane, value) coordinates.
   Its lane part is computed once per operand; everything else is an
   immediate offset or, for the K tile, the loop step. *)

open Layouts

let axis size stride : Linear.t = Axis { size; stride }

(* SM80 m16n8k16 atoms as thread-value -> logical maps over row-major
   tiles; thread coordinates (g, t4) with lane = 4 g + t4. *)
let f_a : Linear.t =
  (* A tile 16 x 16: values (colhalf, rowhalf, pair), register = 2 colhalf + rowhalf *)
  Group [ Group [ axis 8 16; axis 4 2 ]; Group [ axis 2 8; axis 2 128; axis 2 1 ] ]

let f_b : Linear.t =
  (* Bt tile 8 x 16: values (colhalf, pair), register = colhalf *)
  Group [ Group [ axis 8 16; axis 4 2 ]; Group [ axis 2 8; axis 2 1 ] ]

let f_c : Linear.t =
  (* C tile 16 x 8: values (rowhalf, pair), register pair = rowhalf *)
  Group [ Group [ axis 8 8; axis 4 2 ]; Group [ axis 2 64; axis 2 1 ] ]

(* The affine address map of an operand: coefficients by variable name
   and the constant, in elements. *)
type affine =
  { coef : string -> int
  ; const : int
  }

let fragment_map ~(storage : Linear.t) ~(tile : int * int) ~(grid : int * int) ~(f : Linear.t) : affine =
  let st : (Space.logical, Space.physical) Layout.t = Layout.storage storage in
  let tiled = Layout.divide ~by:(Product [ Bound (fst tile); Bound (snd tile) ]) st in
  let w = Linear.canonical (Product [ Bound (fst grid); Bound (snd grid) ]) in
  let fr : (Space.thread_value, Space.logical) Layout.t = Layout.of_linear f in
  let comp = Layout.compose (Layout.interleave ~by:w fr) tiled in
  match Layout.strided_form comp with
  | None -> failwith "fragment map has no strided form"
  | Some e ->
    if not (Expr.is_affine e) then failwith ("fragment map not affine: " ^ Expr.to_string e);
    let const = Expr.eval e (fun _ -> 0) in
    { coef = (fun v -> Expr.eval e (fun x -> if x = v then 1 else 0) - const); const }

(* variable names of the composite's domain: ((ti, tj), ((g, t4), values)) *)
let v_ti = "c0_0" and v_tj = "c0_1" and v_g = "c1_0_0" and v_t4 = "c1_0_1"
let v_val i = Printf.sprintf "c1_1_%d" i

let generate ~m ~n ~k =
  if m mod 16 <> 0 || n mod 8 <> 0 || k mod 16 <> 0 then failwith "M%16, N%8, K%16 must be 0";
  let mt = m / 16 and nt = n / 8 and kt = k / 16 in
  let a = fragment_map ~storage:(Group [ axis m k; axis k 1 ]) ~tile:(16, 16) ~grid:(mt, kt) ~f:f_a in
  let bt = fragment_map ~storage:(Group [ axis n k; axis k 1 ]) ~tile:(8, 16) ~grid:(nt, kt) ~f:f_b in
  let c = fragment_map ~storage:(Group [ axis m n; axis n 1 ]) ~tile:(16, 8) ~grid:(mt, nt) ~f:f_c in
  (* the innermost value coordinate must be contiguous: 32-bit loads of
     two f16, 64-bit stores of two f32 *)
  assert (a.coef (v_val 2) = 1 && bt.coef (v_val 1) = 1 && c.coef (v_val 1) = 1);
  let b = Sass.create () in
  let open Sass in
  (* registers *)
  let r_tid = 0 and r_t4 = 2 and r_g = 3 and r_cnt = 4 in
  let pa = 8 and pb = 10 and pc = 12 in
  let rbase = 16 in
  let acc mi ni = rbase + (4 * ((mi * nt) + ni)) in
  let acc_end = rbase + (4 * mt * nt) in
  let afrag mi = acc_end + (4 * mi) in
  let bfrag ni = acc_end + (4 * mt) + (2 * ni) in
  let top = acc_end + (4 * mt) + (2 * nt) in
  (* the two registers above the highest one used are reserved: ptxas reports
     max index + 3, and writing them faults with an illegal instruction *)
  let nregs = ((top + 2 + 7) / 8) * 8 in
  if nregs > 255 then failwith "register budget exceeded";
  (* prologue *)
  ldc b 1 0x37c;
  s2r_tid b r_tid;
  ldcu64 b 4 0x358;
  ldcu128 b 8 0x380;
  ldcu64 b 12 0x390;
  shf_r b r_g r_tid 2;
  lop3_and b r_t4 r_tid 3;
  (* per-lane byte offset of each operand: elem * (cg g + ct t4) *)
  let lane_base ~elem ~(f : affine) ~scratch ~carry ~ur ~dst =
    imad_rz b scratch r_g (elem * f.coef v_g);
    imad b scratch r_t4 (elem * f.coef v_t4) scratch;
    iadd3_ur b dst ~carry scratch ur;
    imad_x_ur b (dst + 1) (ur + 1) carry
  in
  lane_base ~elem:2 ~f:a ~scratch:5 ~carry:0 ~ur:8 ~dst:pa;
  lane_base ~elem:2 ~f:bt ~scratch:6 ~carry:1 ~ur:10 ~dst:pb;
  lane_base ~elem:4 ~f:c ~scratch:7 ~carry:2 ~ur:12 ~dst:pc;
  for mi = 0 to mt - 1 do
    for ni = 0 to nt - 1 do
      cs2r b (acc mi ni);
      cs2r b (acc mi ni + 2)
    done
  done;
  mov_rz b r_cnt;
  (* immediates, in bytes, at lane 0 and K tile 0 *)
  let imm_a mi j = 2 * (a.const + (mi * a.coef v_ti) + ((j / 2) * a.coef (v_val 0)) + ((j mod 2) * a.coef (v_val 1))) in
  let imm_b ni j = 2 * (bt.const + (ni * bt.coef v_ti) + (j * bt.coef (v_val 0))) in
  let imm_c mi ni j = 4 * (c.const + (mi * c.coef v_ti) + (ni * c.coef v_tj) + (j * c.coef (v_val 0))) in
  let step_a = 2 * a.coef v_tj and step_b = 2 * bt.coef v_tj in
  (* K loop *)
  label b "LOOP";
  for mi = 0 to mt - 1 do
    for j = 0 to 3 do
      ldg b (afrag mi + j) ~base:pa ~imm:(imm_a mi j)
    done
  done;
  for ni = 0 to nt - 1 do
    for j = 0 to 1 do
      ldg b (bfrag ni + j) ~base:pb ~imm:(imm_b ni j)
    done
  done;
  viadd b r_cnt r_cnt 1;
  isetp_lt_u32 b 3 r_cnt kt;
  iadd3_imm b pa ~carry:0 pa step_a;
  imad_x_r b (pa + 1) (pa + 1) 0;
  iadd3_imm b pb ~carry:1 pb step_b;
  imad_x_r b (pb + 1) (pb + 1) 1;
  for mi = 0 to mt - 1 do
    for ni = 0 to nt - 1 do
      hmma b ~d:(acc mi ni) ~a:(afrag mi) ~bb:(bfrag ni) ~c:(acc mi ni)
    done
  done;
  bra b 3 "LOOP";
  (* epilogue *)
  for mi = 0 to mt - 1 do
    for ni = 0 to nt - 1 do
      for j = 0 to 1 do
        stg64 b ~base:pc ~imm:(imm_c mi ni j) ~data:(acc mi ni + (2 * j))
      done
    done
  done;
  exit b;
  let header =
    [ Printf.sprintf "# warp GEMM %dx%dx%d: C f32 = A f16 . B f16, one warp, HMMA.16816" m n k
    ; Printf.sprintf ".kernel gemm_%d_%d_%d" m n k
    ; ".sm sm_100a"
    ; Printf.sprintf ".regs %d" nregs
    ; ".params 8 8 8"
    ]
  in
  header @ Sched.schedule (Sass.items b)
