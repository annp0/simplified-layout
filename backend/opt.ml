(* the options of a GEMM program on the command line *)
type t =
  { bufs : int option
  ; cluster : int
  ; cluster_n : int
  ; pair : bool
  }

let default = { bufs = None; cluster = 1; cluster_n = 1; pair = false }
