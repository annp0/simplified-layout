(* The derivations the compiler makes, checked against what the device and
   ptxas are known to use. Every constant below was either measured on a B200
   or read out of ptxas-compiled SASS; if a derivation drifts from it, this
   fails before a kernel is ever run. *)

open Layouts

let failures = ref 0

let check name ok =
  if not ok then begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end

let raises f = match f () with _ -> false | exception Failure _ -> true

let () =
  (* an MMA operand stage: 128 rows of 64 f16, K-major, 128-byte swizzle *)
  let sa = Atom.swizzled_rows ~rows:128 ~cols:64 ~elem:2 in
  let d = Atom.umma_kmajor sa ~elem:2 ~mma_k:16 in
  check "operand SBO is one 8-row group of 128-byte rows" (d.sbo = 1024);
  check "an MMA k step of 16 f16 advances the start by 32 bytes" (d.kstep = 2);
  (* CUTLASS's mainloop sets exactly this high word: UMOV UR7, 0x40004040 *)
  check "descriptor high word is the one ptxas emits" (Atom.desc_high d = 0x40004040);
  let bx = Atom.tma_box sa ~elem:2 in
  check "operand box" (bx.box_rows = 128 && bx.box_cols = 64 && bx.box_swizzle = 128);
  (* layouts no descriptor or box can express are refused *)
  let plain = Layout.storage (Group [ Axis { size = 128; stride = 128 }; Axis { size = 64; stride = 2 } ]) in
  check "an unswizzled tile has no SWIZZLE_128B descriptor" (raises (fun () -> Atom.umma_kmajor plain ~elem:2 ~mma_k:16));
  check "an unswizzled tile has no SWIZZLE_128B box" (raises (fun () -> Atom.tma_box plain ~elem:2));
  check "a row that is not one swizzle span is refused" (raises (fun () -> Atom.swizzled_rows ~rows:32 ~cols:48 ~elem:2))

let () =
  (* the accumulator's fragment through tcgen05.ld.32x32b.x32 *)
  let rows = 128 and cols = 256 and n = 32 in
  let bm = rows / 32 and bn = cols / n in
  let ld =
    Layout.compose
      (Layout.interleave ~by:(Linear.canonical (Product [ Bound bm; Bound bn ])) (Atom.ldtm_32x32b ~n))
      (Layout.divide ~by:(Product [ Bound 32; Bound n ]) (Atom.tmem_accumulator ~rows ~cols))
  in
  let at w ch l r = Layout.offset ld (Coord.Tuple [ Tuple [ Idx w; Idx ch ]; Tuple [ Idx l; Idx r ] ]) in
  check "tensor-memory load contract" (not (raises (fun () -> Atom.check_ldtm ~at ~blocks_w:bm ~blocks_ch:bn ~n)));
  let base w ch = Layout.offset ld (Coord.Tuple [ Tuple [ Idx w; Idx ch ]; Tuple [ Idx 0; Idx 0 ] ]) in
  (* measured: warp w reads its quarter at + w << 21, chunk ch at + 32 ch *)
  check "block row w starts at tensor-memory lane 32 w" (List.for_all (fun w -> base w 0 = w lsl 21) [ 0; 1; 2; 3 ]);
  check "block column ch starts at column 32 ch" (List.for_all (fun ch -> base 0 ch = 32 * ch) (List.init bn Fun.id))

let () =
  (* the staging write: one warp's 32 x 32 f32 block into the 128-byte
     swizzled box the copy engine reads. On the device, the epilogue that
     stored lane l's vector q at 128 l + 16 (q xor (l mod 8)) was exact. *)
  let box = Atom.swizzled_rows ~rows:32 ~cols:32 ~elem:4 in
  let sts = Layout.compose (Atom.ldtm_32x32b ~n:32) box in
  let ok = ref true in
  for l = 0 to 31 do
    for q = 0 to 7 do
      if Layout.offset sts (Coord.Tuple [ Idx l; Idx (4 * q) ]) <> (128 * l) + (16 * (q lxor (l land 7))) then ok := false
    done
  done;
  check "staging addresses are the ones measured exact on the device" !ok;
  check "staging write is injective" (Layout.is_injective sts);
  (* and what the emitter will be given evaluates to the same, after its
     range-aware rewrites *)
  let range = function "laneid" -> 32 | v -> failwith v in
  let ok = ref true in
  for q = 0 to 7 do
    let e = Restricted.expr (Restricted.restrict ~at:(Parts [ Free; At (4 * q) ]) sts) in
    let e = Emit.simplify range (Emit.inline [] (Expr.bind "c0" (Expr.var "laneid") e)) in
    for l = 0 to 31 do
      if Expr.eval e (fun _ -> l) <> Layout.offset sts (Coord.Tuple [ Idx l; Idx (4 * q) ]) then ok := false
    done
  done;
  check "emitted staging expressions agree with the layout" !ok;
  let bx = Atom.tma_box box ~elem:4 in
  check "store box" (bx.box_rows = 32 && bx.box_cols = 32 && bx.box_elem = 4 && bx.box_swizzle = 128)

let () =
  (* The transposed accumulator's staging write, as cuBLAS's nvjet stages it
     at 8192^3: register r of lane l of a tcgen05.ld.32x32b.x8 is output row
     r, column l, of an 8 x 32 f32 box with the 128-byte swizzle. nvjet's
     STS addresses are 4 l xor (0x90 r) -- (r << 7) + (4 l xor (r << 4)). *)
  let box = Atom.swizzled_rows ~rows:8 ~cols:32 ~elem:4 in
  let sts = Layout.compose (Atom.ldtm_32x32b ~n:8) (Layout.compose (Lower2.transpose ~rows:32 ~cols:8) box) in
  let ok = ref true in
  for l = 0 to 31 do
    for r = 0 to 7 do
      if Layout.offset sts (Coord.Tuple [ Idx l; Idx r ]) <> (4 * l) lxor (0x90 * r) then ok := false
    done
  done;
  check "transposed staging addresses are nvjet's" !ok

let () =
  (* the emitter's exact division, where a tile count is not a power of two *)
  let ok = ref true in
  List.iter
    (fun (d, bound) ->
      let m, sh = Emit.exact_recip d bound in
      for t = 0 to bound - 1 do
        if (t * m) lsr sh <> t / d then ok := false
      done)
    [ 6, 72; 12, 144; 10, 8192; 3, 4096 ];
  check "exact reciprocal divides every index in range" !ok

let () =
  (* the MMA atom: its instruction descriptor against the ones the
     production kernels load, and the rows of each operand a CTA holds *)
  let atom ~m ~n ~ctas =
    Atom.umma ~ab:F16 ~acc:F32 ~m ~n ~ctas ~a_major:K_major ~b_major:K_major ~a_src:Smem_desc
  in
  (* CUTLASS 70's SM100_MMA_F16BF16_2x1SM_SS<half,half,float,256,128>: UMOV 0x10200010 *)
  check "idesc of the 256 x 128 pair MMA is CUTLASS's" (Atom.idesc (atom ~m:256 ~n:128 ~ctas:2) = 0x10200010);
  (* cuBLAS's nvjet_hss_128x256_64x6_2x1_2cta at 8192^3: UMOV UR15, 0x10400010 *)
  check "idesc of the 256 x 256 pair MMA is nvjet's" (Atom.idesc (atom ~m:256 ~n:256 ~ctas:2) = 0x10400010);
  check "K of an f16 MMA is 16" (Atom.umma_k (atom ~m:128 ~n:256 ~ctas:1) = 16);
  let u = atom ~m:256 ~n:128 ~ctas:2 in
  let rows l ~cols v = Atom.cta_rows l ~cols ~v in
  check "the pair splits A's rows in halves"
    (rows (Atom.umma_a u) ~cols:16 0 = (0, 128) && rows (Atom.umma_a u) ~cols:16 1 = (128, 128));
  check "the pair splits B's rows in halves"
    (rows (Atom.umma_b u) ~cols:16 0 = (0, 64) && rows (Atom.umma_b u) ~cols:16 1 = (64, 64));
  check "the pair splits the result's rows" (rows (Atom.umma_c u) ~cols:128 1 = (128, 128));
  check "one CTA takes M of 64 or 128 only" (raises (fun () -> atom ~m:256 ~n:128 ~ctas:1));
  check "a pair takes N in steps of 16" (raises (fun () -> atom ~m:256 ~n:136 ~ctas:2));
  check "A from tensor memory is K-major"
    (raises (fun () -> Atom.umma ~ab:F16 ~acc:F32 ~m:128 ~n:128 ~ctas:1 ~a_major:MN_major ~b_major:K_major ~a_src:Tmem))

let () =
  (* every compiled GEMM checks its own derivations; compiling them here
     runs those checks over the shapes the benchmarks use *)
  List.iter
    (fun (m, n, k) ->
      let tile_n = Dsl2.choose_tile_n ~m ~n ~tile_m:128 in
      check (Printf.sprintf "compiles %dx%dx%d" m n k)
        (not (raises (fun () -> Lower2.lower (Dsl2.gemm ~tile_n ~m ~n ~k ~depth:4 ())))))
    [ 1024, 1024, 1024; 1536, 1536, 1536; 2048, 2048, 2048; 4096, 4096, 4096; 3072, 1280, 2048 ];
  (* and the configuration the chooser picks for each benchmark shape *)
  List.iter
    (fun (m, n, k) ->
      let c = Dsl2.choose ~m ~n ~k in
      check (Printf.sprintf "compiles the chosen %dx%dx%d" m n k)
        (not
           (raises (fun () ->
              Lower2.lower
                (Dsl2.gemm ~tile_n:c.c_tile_n ~cluster:c.c_cluster ~pair:c.c_pair ~m ~n ~k ~depth:c.c_depth ())))))
    [ 1024, 1024, 1024; 1536, 1536, 1536; 2048, 2048, 2048; 4096, 4096, 4096; 4096, 4096, 1024; 3072, 1280, 2048
    ; 8192, 2048, 4096; 8192, 8192, 8192 ];
  if !failures > 0 then (Printf.printf "%d derivation checks failed\n" !failures; exit 1)
  else print_endline "derivations: every check passed"
