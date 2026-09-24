let usage () =
  prerr_endline
    "usage: warpc gemm M N K                  (the configuration the measurements favour)\n\
    \       warpc pgemm M N K DEPTH [TILE_N] [--bufs B] [--cluster X Y] [--pair] [--swap] [--clc] [--tile-m M]\n\
    \       warpc ptma|pepi M N K        warpc pmma M N K DEPTH\n\
    \       warpc umma M N K             (the first DSL, tcgen05)\n\
    \       warpc hmma M N K             (SM80 fragments)";
  exit 2

let int = int_of_string

(* the options a GEMM program takes; each is part of the program, so it is a
   flag here rather than something the compiler reads from the environment *)
let rec options acc = function
  | [] -> acc
  | "--bufs" :: b :: rest -> options { acc with Opt.bufs = Some (int b) } rest
  | "--cluster" :: x :: y :: rest -> options { acc with Opt.cluster = int x; cluster_n = int y } rest
  | "--pair" :: rest -> options { acc with Opt.pair = true } rest
  | "--swap" :: rest -> options { acc with Opt.swap = true } rest
  | "--clc" :: rest -> options { acc with Opt.clc = true } rest
  | "--debug-waits" :: rest -> Lower2.debug_waits := true; options acc rest
  | "--tile-m" :: t :: rest -> options { acc with Opt.tile_m = int t } rest
  | _ -> usage ()

let () =
  match Array.to_list Sys.argv with
  | [ _; "hmma"; m; n; k ] -> List.iter print_endline (Gemm.generate ~m:(int m) ~n:(int n) ~k:(int k))
  | [ _; "gemm"; m; n; k ] ->
    (* the configuration the measurements favour for this shape *)
    let m = int m and n = int n and k = int k in
    let kernel = Dsl2.of_config (Dsl2.choose ~m ~n ~k) ~m ~n ~k in
    List.iter print_endline (Lower2.lower kernel)
  | _ :: "pgemm" :: m :: n :: k :: depth :: rest ->
    let m = int m and n = int n in
    let tile_n, rest =
      match rest with
      | t :: rest when String.length t > 0 && t.[0] <> '-' -> int t, rest
      | rest -> Dsl2.choose_tile_n ~m ~n ~tile_m:128, rest
    in
    let o = options Opt.default rest in
    let kernel =
      Dsl2.gemm ~tile_m:o.tile_m ~tile_n ?bufs:o.bufs ~cluster:o.cluster ~cluster_n:o.cluster_n ~pair:o.pair ~swap:o.swap ~clc:o.clc
        ~m ~n ~k:(int k) ~depth:(int depth) ()
    in
    List.iter print_endline (Lower2.lower kernel)
  | [ _; "ptma"; m; n; k ] -> List.iter print_endline (Lower2.lower (Dsl2.tma_probe ~m:(int m) ~n:(int n) ~k:(int k)))
  | [ _; "pmma"; m; n; k; d ] ->
    List.iter print_endline (Lower2.lower (Dsl2.mma_probe ~m:(int m) ~n:(int n) ~k:(int k) ~depth:(int d)))
  | [ _; "pepi"; m; n; k ] -> List.iter print_endline (Lower2.lower (Dsl2.epi_probe ~m:(int m) ~n:(int n) ~k:(int k)))
  | [ _; "pclcloop"; f ] -> List.iter print_endline (Lower2.clc_loop_probe ~first:(int f) ())
  | [ _; "pclcloop"; f; style ] when String.length style = 3 ->
    (* three switches: register-addressed barriers, a wide answer read, cluster-form operands *)
    Lower2.clc_style := { gpr_bars = style.[0] = '1'; wide = style.[1] = '1'; cluster_ops = style.[2] = '1' };
    List.iter print_endline (Lower2.clc_loop_probe ~first:(int f) ())
  | [ _; "talloc"; n ] -> List.iter print_endline (Lower2.tmem_probe ~ncols:(int n) ~times:1)
  | [ _; "talloc"; n; t ] -> List.iter print_endline (Lower2.tmem_probe ~ncols:(int n) ~times:(int t))
  | [ _; "umma"; m; n; k ] -> List.iter print_endline (Lower.lower (Dsl.gemm ~m:(int m) ~n:(int n) ~k:(int k)))
  | _ -> usage ()
