(* The DSL, second cut: a kernel is a set of warp roles over shared tiles,
   tensor-memory accumulators and pipes (mbarriers). Global operands arrive by
   TMA into a ring of stages; the tensor core reads the stages and writes
   tensor memory; the accumulator leaves through a staging tile by tensor-map
   store; a K loop advances the ring.

   Layouts are never written. A tile is declared by shape; the instruction
   that consumes it fixes its layout, and every copy is compiled from the
   layouts of its two ends (see Atom, Lower2). *)

type dtype =
  | F16
  | F32

type via =
  | Ptr (* a plain pointer parameter *)
  | Tmap (* a pointer to a tensor map for TMA *)

type gmat =
  { name : string
  ; dtype : dtype
  ; rows : int
  ; cols : int (* row-major, leading dimension = cols *)
  ; via : via
  }

(* how many copies of a shared tile there are: one per stage of the k-loop
   ring, or [n] for each warp that writes the tile *)
type ring =
  | Stages
  | Per_warp of int

(* A shared tile has a shape and no layout: the instruction that consumes it
   fixes its layout (an MMA operand, a tensor-map box), see Atom. *)
type stile =
  { sname : string
  ; sdtype : dtype
  ; srows : int
  ; scols : int (* one copy; for a stage, the K extent of the stage *)
  ; ring : ring
  }

type ttile =
  { tname : string
  ; trows : int
  ; tcols : int
  ; bufs : int (* accumulators in flight: the epilogue of one tile runs while
                  the mainloop of the next fills the other *)
  }

type pipe =
  { pname : string
  ; per_stage : bool
  ; per_buffer : bool (* one barrier per accumulator buffer *)
  ; cross : bool (* every CTA of the cluster must have signalled before a waiter passes *)
  ; arrivals : int (* arrivals that complete a phase: warps signalling, or 1 for TMA / tensor-core commits *)
  ; free_at_start : bool (* the first wait passes: a ring slot that starts empty *)
  }

type coord =
  | Tile_m
  | Tile_n

type stmt =
  | Tma of
      { dst : string
      ; src : string
      ; rows : coord
      ; pipe : string
      }
  | Wait of string
  | Mma of
      { d : string
      ; a : string
      ; b : string
      }
  | Commit of string
  | Signal of string
  | Store of
      { dst : string (* a global matrix, written by tensor map *)
      ; src : string (* a tensor-memory accumulator *)
      ; via : string
          (* the shared tile the accumulator passes through: each warp reads
             its fragment out of tensor memory, writes it into its copy of
             [via], and the copy engine stores that to [dst] *)
      ; release : string option (* signalled once the accumulator has been read *)
      }
  | Kloop of stmt list
  | Role of int list * stmt list

type kernel =
  { name : string
  ; params : gmat list
  ; smem : stile list
  ; depth : int
  ; tmem : ttile list
  ; pipes : pipe list
  ; nwarps : int
  ; cluster : int (* CTAs along M: the pair a two-CTA MMA splits its rows over *)
  ; cluster_n : int (* CTAs along N: the pairs that share the same operand rows *)
  ; pair : bool (* one MMA over a CTA pair: each CTA holds half of each operand *)
  ; tile_m : int
  ; tile_n : int
  ; tile_k : int
  ; k_total : int
  ; tile_m_count : int
  ; tile_n_count : int
  ; body : stmt list
  }

(* The wide tile moves fewer operand bytes per output, but it also makes fewer
   tiles; below about half a machine's worth the idle multiprocessors cost more
   than the traffic saves. Measured at 1024 cubed: 162 wide against 251 narrow;
   at 2048 cubed: 1003 wide against 873 narrow. *)
(* a wider tile amortises the operand traffic, but only if there are still
   enough tiles to cover the machine: below one wave the narrow tile wins
   because it doubles the tiles and fills the idle multiprocessors *)
(* the multiprocessors of a B200 *)
let sms = 148

let choose_tile_n ~m ~n ~tile_m =
  if n mod 256 <> 0
  then 128
  else (
    (* how much of a wave the wide tile leaves busy: below about three
       fifths the narrow tile wins, because doubling the tiles fills the
       multiprocessors the wide one leaves idle *)
    let tiles = m / tile_m * (n / 256) in
    let waves = ((tiles + sms - 1) / sms) * sms in
    if 5 * tiles < 3 * waves then 128 else 256)

let gemm ?(tile_m = 128) ?(tile_n = 128) ?(tile_k = 64) ?bufs ?(cluster = 1) ?(cluster_n = 1) ?(pair = false)
    ~m ~n ~k ~depth () =
  let bsplit = if pair then 2 else 1 in
  { name = Printf.sprintf "pgemm_%d_%d_%d_s%d_t%d" m n k depth tile_n
  ; params =
      [ { name = "c"; dtype = F32; rows = m; cols = n; via = Tmap }
      ; { name = "a"; dtype = F16; rows = m; cols = k; via = Tmap }
      ; { name = "bt"; dtype = F16; rows = n; cols = k; via = Tmap }
      ]
    (* A two-CTA MMA splits BOTH operands over the pair: each CTA supplies half
       of the rows and half of the columns, and the tensor core reads across
       the pair.  Established from the hardware and from CUTLASS: with the full
       column tile in each CTA every output column past the halfway point is
       wrong, and half of it per CTA is what makes their 230 KB of shared
       memory hold eight stages. *)
  ; smem =
      [ { sname = "sa"; sdtype = F16; srows = tile_m; scols = tile_k; ring = Stages }
      ; { sname = "sb"; sdtype = F16; srows = tile_n / bsplit; scols = tile_k; ring = Stages }
        (* one 32 x 32 block of the accumulator per warp, two deep so a block
           is written while the copy engine still reads the previous one *)
      ; { sname = "sc"; sdtype = F32; srows = 32; scols = 32; ring = Per_warp 2 }
      ]
  ; depth
  ; tmem =
      [ { tname = "acc"
        ; trows = tile_m
        ; tcols = tile_n
        ; (* Two accumulators let the epilogue of one tile run while the
             mainloop of the next fills the other; two 256-wide ones fill
             tensor memory exactly. A CTA with one tile has no next tile, and
             the second allocation is only cost: measured, 972 against 889 at
             2048 cubed. *)
          bufs =
            (match bufs with
             | Some b -> b
             | None -> if 2 * tile_n <= 512 && m / tile_m * (n / tile_n) > sms then 2 else 1)
        } ]
  ; pipes =
      [ { pname = "full"; per_stage = true; per_buffer = false; cross = false; arrivals = 1; free_at_start = false }
        (* a stage is refilled by every CTA of the cluster, so it is free only
           once every CTA has finished reading it *)
      ; { pname = "empty"; per_stage = true; per_buffer = false; cross = true; arrivals = 1; free_at_start = true }
      ; { pname = "ready"; per_stage = false; per_buffer = true; cross = false; arrivals = 1; free_at_start = false }
      ; { pname = "free"; per_stage = false; per_buffer = true; cross = false; arrivals = 4; free_at_start = true }
      ]
  ; nwarps = 8
    (* A cluster and a two-CTA MMA are built but not yet correct: the default
       is a single CTA per tile. *)
  ; cluster
  ; cluster_n
  ; pair
  ; tile_m; tile_n; tile_k; k_total = k; tile_m_count = m / tile_m; tile_n_count = n / tile_n
  ; body =
      [ Role ([ 0 ], [ Kloop [ Wait "empty"; Tma { dst = "sa"; src = "a"; rows = Tile_m; pipe = "full" }; Tma { dst = "sb"; src = "bt"; rows = Tile_n; pipe = "full" } ] ])
      ; Role
          ( [ 1 ]
          , [ Wait "free"; Kloop [ Wait "full"; Mma { d = "acc"; a = "sa"; b = "sb" }; Commit "empty" ]; Commit "ready" ] )
      ; Role ([ 4; 5; 6; 7 ], [ Wait "ready"; Store { dst = "c"; src = "acc"; via = "sc"; release = Some "free" } ])
      ]
  }

(* a probe keeps only the shared tiles its body touches: a tile nothing reads
   has no instruction to fix its layout *)
let only_used (k : kernel) =
  let rec names acc = function
    | Tma { dst; _ } -> dst :: acc
    | Mma { a; b; _ } -> a :: b :: acc
    | Store { via; _ } -> via :: acc
    | Kloop body | Role (_, body) -> List.fold_left names acc body
    | _ -> acc
  in
  let used = List.fold_left names [] k.body in
  { k with smem = List.filter (fun (t : stile) -> List.mem t.sname used) k.smem }

(* a probe: warp 0 loads one k tile by TMA and waits for it to land *)
let tma_probe ~m ~n ~k =
  let g = gemm ~m ~n ~k ~depth:1 () in
  only_used
  { g with
    name = Printf.sprintf "ptma_%d_%d_%d_s1" m n k
  ; body = [ Role ([ 0 ], [ Kloop [ Wait "empty"; Tma { dst = "sa"; src = "a"; rows = Tile_m; pipe = "full" }; Tma { dst = "sb"; src = "bt"; rows = Tile_n; pipe = "full" }; Wait "full" ] ]) ]
  }

(* probes: MMAs without the epilogue; the epilogue without MMAs *)
let mma_probe ~m ~n ~k ~depth =
  let g = gemm ~m ~n ~k ~depth () in
  only_used
  { g with
    name = Printf.sprintf "pmma_%d_%d_%d_s%d" m n k depth
  ; body =
      [ Role ([ 0 ], [ Kloop [ Wait "empty"; Tma { dst = "sa"; src = "a"; rows = Tile_m; pipe = "full" }; Tma { dst = "sb"; src = "bt"; rows = Tile_n; pipe = "full" } ] ])
      ; Role ([ 1 ], [ Kloop [ Wait "full"; Mma { d = "acc"; a = "sa"; b = "sb" }; Commit "empty" ]; Commit "ready"; Wait "ready" ]) ] }

let epi_probe ~m ~n ~k =
  let g = gemm ~m ~n ~k ~depth:1 () in
  only_used
  { g with
    name = Printf.sprintf "pepi_%d_%d_%d_s1" m n k
  ; body = [ Role ([ 1 ], [ Commit "ready"; Wait "free" ]); Role ([ 4; 5; 6; 7 ], [ Wait "ready"; Store { dst = "c"; src = "acc"; via = "sc"; release = Some "free" } ]) ] }

let dtype_string = function F16 -> "f16" | F32 -> "f32"
let coord_string = function Tile_m -> "tile_m" | Tile_n -> "tile_n"

let rec stmt_string ind = function
  | Tma { dst; src; rows; pipe } -> Printf.sprintf "%s%s[stage] <- tma %s[%s rows, k tile]  -> %s" ind dst src (coord_string rows) pipe
  | Wait p -> ind ^ "wait " ^ p
  | Mma { d; a; b } -> Printf.sprintf "%s%s += %s[stage] . %s[stage]^T" ind d a b
  | Commit p -> ind ^ "commit " ^ p
  | Signal p -> ind ^ "signal " ^ p
  | Store { dst; src; via; release } ->
    Printf.sprintf "%s%s[tile] <- %s via %s%s" ind dst src via
      (match release with None -> "" | Some p -> ", then " ^ p)
  | Kloop body -> Printf.sprintf "%sfor each k tile (stage = k mod depth)\n%s" ind (String.concat "\n" (List.map (stmt_string (ind ^ "  ")) body))
  | Role (ws, body) ->
    Printf.sprintf "%swarps %s\n%s" ind (String.concat "," (List.map string_of_int ws)) (String.concat "\n" (List.map (stmt_string (ind ^ "  ")) body))

let to_string k =
  String.concat
    "\n"
    ([ Printf.sprintf "kernel %s (%s)" k.name
         (String.concat ", " (List.map (fun (g : gmat) -> Printf.sprintf "%s : %s[%d,%d]%s" g.name (dtype_string g.dtype) g.rows g.cols (if g.via = Tmap then " via tma" else "")) k.params))
     ; Printf.sprintf "  tile %dx%d, k tile %d, ring depth %d, %d warps, cluster %dx%d%s" k.tile_m k.tile_n k.tile_k
         k.depth k.nwarps k.cluster k.cluster_n (if k.pair then ", two-CTA MMA" else "") ]
     @ List.map
         (fun (s : stile) ->
           Printf.sprintf "  smem %s : %s[%d,%d] x %s" s.sname (dtype_string s.sdtype) s.srows s.scols
             (match s.ring with Stages -> "depth" | Per_warp n -> Printf.sprintf "%d per warp" n))
         k.smem
     @ List.map (fun (t : ttile) -> Printf.sprintf "  tmem %s : f32[%d,%d] x %d buffers" t.tname t.trows t.tcols t.bufs) k.tmem
     @ List.map (fun (p : pipe) -> Printf.sprintf "  pipe %s%s, %d arrival%s%s" p.pname (if p.per_stage then "[stage]" else if p.per_buffer then "[buffer]" else "") p.arrivals (if p.arrivals > 1 then "s" else "") (if p.free_at_start then ", free at start" else "")) k.pipes
     @ List.map (stmt_string "  ") k.body)
