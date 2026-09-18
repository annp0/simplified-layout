(* The DSL: a kernel is a program every warp of the CTA runs. Tiles live in
   global memory (parameters), shared memory, or tensor memory; a copy is
   an assignment between tiles; mma multiplies two shared-memory tiles into
   a tensor-memory tile. Layouts are never written: mma fixes the layouts
   of its operands, and copies are compiled from the layouts of both ends. *)

type dtype =
  | F16
  | F32

type mat =
  { name : string
  ; dtype : dtype
  ; rows : int
  ; cols : int (* row-major *)
  }

type rows =
  | All
  | Rows_of_warp (* the 32 rows a warp owns: 32 w .. 32 w + 31 *)

type ref_ =
  { tile : string
  ; rows : rows
  ; ktile : string option (* the columns [16 v, 16 v + 16) for loop variable v *)
  }

type stmt =
  | Copy of ref_ * ref_ (* dst <- src *)
  | Mma of
      { d : string
      ; a : string
      ; b : string
      } (* d += a . b^T ; the first mma into d overwrites it *)
  | Commit of string (* the mma issued so far arrive on the pipe when complete *)
  | Wait of string (* block until the pipe's current phase completes *)
  | Fence_barrier (* shared-memory writes visible to every warp and to the tensor core *)
  | For of string * int * stmt list
  | Warp of int * stmt list (* only this warp runs the body *)

type kernel =
  { name : string
  ; params : mat list
  ; smem : mat list
  ; tmem : mat list
  ; pipes : string list
  ; nwarps : int
  ; body : stmt list
  }

let mat name dtype rows cols = { name; dtype; rows; cols }
let all t = { tile = t; rows = All; ktile = None }
let at t v = { tile = t; rows = All; ktile = Some v }
let mine t = { tile = t; rows = Rows_of_warp; ktile = None }

(* C[m x n] f32 = A[m x k] f16 . B, B given as Bt[n x k]; the K loop is over
   16-wide tiles staged through shared memory, one tile at a time *)
let gemm ~m ~n ~k =
  { name = Printf.sprintf "umma_%d_%d_%d" m n k
  ; params = [ mat "a" F16 m k; mat "bt" F16 n k; mat "c" F32 m n ]
  ; smem = [ mat "sa" F16 m 16; mat "sb" F16 n 16 ]
  ; tmem = [ mat "acc" F32 m n ]
  ; pipes = [ "done" ]
  ; nwarps = 4
  ; body =
      [ For
          ( "kk"
          , k / 16
          , [ Copy (all "sa", at "a" "kk")
            ; Copy (all "sb", at "bt" "kk")
            ; Fence_barrier
            ; Warp (0, [ Mma { d = "acc"; a = "sa"; b = "sb" }; Commit "done" ])
            ; Wait "done"
            ] )
      ; Copy (mine "c", mine "acc")
      ]
  }

let dtype_string = function F16 -> "f16" | F32 -> "f32"
let mat_string (m : mat) = Printf.sprintf "%s : %s[%d,%d]" m.name (dtype_string m.dtype) m.rows m.cols

let ref_string r =
  let rows = match r.rows with All -> "" | Rows_of_warp -> "[rows of warp]" in
  let k = match r.ktile with None -> "" | Some v -> Printf.sprintf "[:, %s]" v in
  r.tile ^ rows ^ k

let rec stmt_string ind = function
  | Copy (d, s) -> Printf.sprintf "%s%s <- %s" ind (ref_string d) (ref_string s)
  | Mma { d; a; b } -> Printf.sprintf "%s%s += %s . %s^T" ind d a b
  | Commit p -> Printf.sprintf "%scommit %s" ind p
  | Wait p -> Printf.sprintf "%swait %s" ind p
  | Fence_barrier -> ind ^ "fence_barrier"
  | For (v, n, body) ->
    Printf.sprintf "%sfor %s in 0 .. %d\n%s" ind v (n - 1) (String.concat "\n" (List.map (stmt_string (ind ^ "  ")) body))
  | Warp (w, body) ->
    Printf.sprintf "%swarp %d\n%s" ind w (String.concat "\n" (List.map (stmt_string (ind ^ "  ")) body))

let to_string k =
  String.concat
    "\n"
    ([ Printf.sprintf "kernel %s (%s)" k.name (String.concat ", " (List.map mat_string k.params)) ]
     @ List.map (fun m -> "  smem " ^ mat_string m) k.smem
     @ List.map (fun m -> "  tmem " ^ mat_string m) k.tmem
     @ List.map (fun p -> "  pipe " ^ p) k.pipes
     @ [ Printf.sprintf "  warps %d" k.nwarps ]
     @ List.map (stmt_string "  ") k.body)
