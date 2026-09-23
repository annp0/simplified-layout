let usage () =
  prerr_endline
    "usage: warpc pgemm M N K DEPTH [TILE_N] [--bufs B] [--cluster X Y] [--pair]\n\
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
  | _ -> usage ()

let () =
  match Array.to_list Sys.argv with
  | [ _; "hmma"; m; n; k ] -> List.iter print_endline (Gemm.generate ~m:(int m) ~n:(int n) ~k:(int k))
  | _ :: "pgemm" :: m :: n :: k :: depth :: rest ->
    let m = int m and n = int n in
    let tile_n, rest =
      match rest with
      | t :: rest when String.length t > 0 && t.[0] <> '-' -> int t, rest
      | rest -> Dsl2.choose_tile_n ~m ~n ~tile_m:128, rest
    in
    let o = options Opt.default rest in
    let kernel =
      Dsl2.gemm ~tile_n ?bufs:o.bufs ~cluster:o.cluster ~cluster_n:o.cluster_n ~pair:o.pair ~m ~n ~k:(int k)
        ~depth:(int depth) ()
    in
    List.iter print_endline (Lower2.lower kernel)
  | [ _; "ptma"; m; n; k ] -> List.iter print_endline (Lower2.lower (Dsl2.tma_probe ~m:(int m) ~n:(int n) ~k:(int k)))
  | [ _; "pmma"; m; n; k; d ] ->
    List.iter print_endline (Lower2.lower (Dsl2.mma_probe ~m:(int m) ~n:(int n) ~k:(int k) ~depth:(int d)))
  | [ _; "pepi"; m; n; k ] -> List.iter print_endline (Lower2.lower (Dsl2.epi_probe ~m:(int m) ~n:(int n) ~k:(int k)))
  | [ _; "talloc"; n ] -> List.iter print_endline (Lower2.tmem_probe ~ncols:(int n) ~times:1)
  | [ _; "talloc"; n; t ] -> List.iter print_endline (Lower2.tmem_probe ~ncols:(int n) ~times:(int t))
  | [ _; "umma"; m; n; k ] -> List.iter print_endline (Lower.lower (Dsl.gemm ~m:(int m) ~n:(int n) ~k:(int k)))
  | _ -> usage ()
