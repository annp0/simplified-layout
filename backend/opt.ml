(* the options of a GEMM program on the command line *)
type t =
  { bufs : int option
  ; cluster : int
  ; cluster_n : int
  ; pair : bool
  ; swap : bool
  ; tile_m : int
  ; clc : bool
  ; clc_slots : int
  ; epi_rows : int
  ; ask_ahead : bool
  }

let default = { bufs = None; cluster = 1; cluster_n = 1; pair = false; swap = false; tile_m = 128; clc = false; clc_slots = 1; epi_rows = 8; ask_ahead = false }
