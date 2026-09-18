let usage () =
  prerr_endline "usage: warpc umma M N K   (tcgen05 path, from the DSL)\n       warpc hmma M N K   (SM80 fragment path)";
  exit 2

let () =
  match Array.to_list Sys.argv with
  | [ _; "hmma"; m; n; k ] ->
    List.iter print_endline (Gemm.generate ~m:(int_of_string m) ~n:(int_of_string n) ~k:(int_of_string k))
  | [ _; "pgemm"; m; n; k; depth ] ->
    let m = int_of_string m and n = int_of_string n in
    let kernel =
      Dsl2.gemm ~tile_n:(Dsl2.choose_tile_n ~m ~n ~tile_m:128) ~m ~n ~k:(int_of_string k) ~depth:(int_of_string depth) ()
    in
    List.iter print_endline (Lower2.lower kernel)
  | [ _; "pgemm"; m; n; k; depth; tile_n ] ->
    let kernel =
      Dsl2.gemm ~tile_n:(int_of_string tile_n) ~m:(int_of_string m) ~n:(int_of_string n) ~k:(int_of_string k)
        ~depth:(int_of_string depth) ()
    in
    List.iter print_endline (Lower2.lower kernel)
  | [ _; "ptma"; m; n; k ] ->
    List.iter print_endline (Lower2.lower (Dsl2.tma_probe ~m:(int_of_string m) ~n:(int_of_string n) ~k:(int_of_string k)))
  | [ _; "pmma"; m; n; k; d ] ->
    List.iter print_endline (Lower2.lower (Dsl2.mma_probe ~m:(int_of_string m) ~n:(int_of_string n) ~k:(int_of_string k) ~depth:(int_of_string d)))
  | [ _; "pepi"; m; n; k ] ->
    List.iter print_endline (Lower2.lower (Dsl2.epi_probe ~m:(int_of_string m) ~n:(int_of_string n) ~k:(int_of_string k)))
  | [ _; "umma"; m; n; k ] ->
    let kernel = Dsl.gemm ~m:(int_of_string m) ~n:(int_of_string n) ~k:(int_of_string k) in
    List.iter print_endline (Lower.lower kernel)
  | _ -> usage ()
