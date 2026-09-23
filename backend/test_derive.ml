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
  check "tensor-memory load contract" (not (raises (fun () -> Atom.check_ldtm ld ~blocks_m:bm ~blocks_n:bn ~n)));
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
  (* every compiled GEMM checks its own derivations; compiling them here
     runs those checks over the shapes the benchmarks use *)
  List.iter
    (fun (m, n, k) ->
      let tile_n = Dsl2.choose_tile_n ~m ~n ~tile_m:128 in
      check (Printf.sprintf "compiles %dx%dx%d" m n k)
        (not (raises (fun () -> Lower2.lower (Dsl2.gemm ~tile_n ~m ~n ~k ~depth:4 ())))))
    [ 1024, 1024, 1024; 1536, 1536, 1536; 2048, 2048, 2048; 4096, 4096, 4096; 3072, 1280, 2048 ];
  if !failures > 0 then (Printf.printf "%d derivation checks failed\n" !failures; exit 1)
  else print_endline "derivations: every check passed"
