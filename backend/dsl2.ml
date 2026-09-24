(* The DSL, second cut: a kernel is a set of warp roles over shared tiles,
   tensor-memory accumulators and pipes (mbarriers). Global operands arrive by
   TMA into a ring of stages; the tensor core reads the stages and writes
   tensor memory; the accumulator leaves through a staging tile by tensor-map
   store; a K loop advances the ring.

   Layouts are never written. A tile is declared by shape; the instruction
   that consumes it fixes its layout, and every copy is compiled from the
   layouts of its two ends (see Atom, Lower2). *)

type dtype = Atom.elt =
  | F16
  | BF16
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
  ; trows : int (* the lanes of one atom's block of the result *)
  ; tcols : int
  ; reps : int
      (* blocks of the result stacked along the MMA's rows, one atom each:
         block r's lanes are the same, its columns r * tcols further on *)
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
      { atom : Atom.umma
          (* the instruction: it fixes the operands' layouts, which CTA holds
             which of their rows, and the accumulator's *)
      ; d : string (* d[i, j] += a[i, k] b[j, k] *)
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
  | Schedule
      (* the tile scheduler: take the tiles of clusters that have not been
         launched yet (cluster launch control) and hand them to every role
         of the cluster *)
  | Kloop of stmt list
  | Role of int list * stmt list

(* How a CTA finds its tiles. [Stride]: a grid of one CTA per multiprocessor,
   each walking the tiles a grid apart. [Clc n]: a grid of every tile, the
   first cluster's scheduler cancelling clusters not yet launched and taking
   their tiles, its answers in a ring of [n] slots every role of the cluster
   reads -- how CUTLASS's and cuBLAS's Blackwell kernels are persistent. *)
type tiles =
  | Stride
  | Clc of int

type kernel =
  { name : string
  ; params : gmat list
  ; smem : stile list
  ; depth : int
  ; tmem : ttile list
  ; pipes : pipe list
  ; nwarps : int
  ; cluster : int (* CTAs along M: the CTAs one MMA spans *)
  ; cluster_n : int (* CTAs along N: the groups that share the same operand rows *)
  ; tiles : tiles
  ; ask_ahead : bool
      (* the tensor-core warp asks whether the next stage has landed before it
         issues this stage's MMAs, as nvjet's does: the MMAs go out while the
         try-wait is answered. It pays when issue, not data, bounds the loop
         (the M = 128 pair at 1024^3, 4384 ns against 4576) and costs when the
         loads do: there the try-wait holds the warp until the next stage lands
         (1536^3, 9568 against 7520). *)
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

(* how many clusters of this many CTAs a B200 holds at once, one CTA a
   multiprocessor: a cluster lives in one GPC, and the GPCs do not divide
   into fours and eights evenly (cuOccupancyMaxActiveClusters, measured) *)
let resident_clusters = function 1 -> sms | 2 -> 74 | 4 -> 33 | 8 -> 15 | c -> failwith (Printf.sprintf "resident_clusters %d" c)

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

(* The GEMM configuration the measurements favour (B200, fp16 in, fp32 out,
   against CUTLASS 70_blackwell_fp16_gemm in the same session):

   - a two-CTA MMA on a 2x1 cluster, 128 x 128 per CTA, ring depth 8: the pair
     splits both operands, so a CTA moves the operand bytes of a 128 x 256 tile
     while the grid has the granularity of a 128 x 128 one. It wins at every
     measured shape but the two below; 2048^3 1020 against 1001 on one CTA,
     4096^3 1545 against 1390, 4096x4096x1024 1086 against 968.
   - one CTA per 128 x 256 tile, ring depth 4, when all three dimensions are
     large: 12288^3 1486 against 1401 on the pair, 16384^3 1600 against 1414.
     16384x16384x4096, 8192x8192x16384 and 16384x8192x8192 still prefer the
     pair, so the rule is on the smallest dimension.

   - one CTA per 128 x 64 tile, ring depth 8, when 128-wide tiles would fill
     at most half the machine and 64-wide ones still fit in one wave: there the
     kernel is latency, and twice the multiprocessors beat a wider tile.
     1024^3 337 against 256 on the pair or on 128 x 128; above that the
     narrow tile loses (2048^3 680 against 1027).

   The pair needs M in pairs of 128-row tiles and a ring that divides the k
   tiles of a persistent kernel; a shape that does not fit falls back to one
   CTA. *)
type config =
  { c_tile_m : int
  ; c_tile_n : int
  ; c_depth : int
  ; c_cluster : int
  ; c_pair : bool
  ; c_swap : bool
  ; c_clc : bool
  ; c_ask_ahead : bool
  ; c_cluster_n : int
  }

let old_config ~tile_n ~depth ~cluster ~pair =
  { c_tile_m = 128; c_tile_n = tile_n; c_depth = depth; c_cluster = cluster; c_pair = pair; c_swap = false; c_clc = false
  ; c_ask_ahead = false; c_cluster_n = 1 }

let swapped ?(cluster_n = 1) ~tile_m ~tile_n ~depth ~clc ~ask_ahead () =
  { c_tile_m = tile_m; c_tile_n = tile_n; c_depth = depth; c_cluster = 2; c_pair = true; c_swap = true; c_clc = clc
  ; c_ask_ahead = ask_ahead; c_cluster_n = cluster_n }

(* cuBLAS's kernels at these shapes, transcribed (nvjet_hss_*_2cta, read from
   their SASS and their binaries' control words): a two-CTA MMA with B^T as
   its A operand, so a CTA's accumulator is output columns by output rows.
   Device time against cuBLAS's best algorithm, nsys, one B200:
   - 8192 and up in every dimension: 256 x 256 a CTA, two stacked M = 256,
     N = 256 atoms, ring depth 4, cluster launch control, asking a stage ahead
     (nvjet_hss_256x256_64x4): 8192^3 544.4 us against 548.1; 16384^3 4.83 ms
     against 4.73.
   - otherwise, when 256-row tiles still fill the machine: N = 192, depth 7
     (nvjet_hss_128x192_64x7), taking tiles by cluster launch control once K
     is long enough to hide the answer's latency: 4096^3 74.8 us against 75.8,
     8192x2048x4096 74.8 against 76.7; with a fixed grid at 4096x4096x1024,
     26.0 against 27.2 (27.0 with the scheduler).
   - when 128 x 128 tiles would fill at most half the machine: the M = 128
     pair, 64 x 128 a CTA, depth 13, asking ahead (nvjet_hss_64x128_64x13):
     1024^3 4384 ns against 4960.
   - when 128 x 128 tiles take more than one wave: 128 x 128 a CTA, depth 8,
     2 x 2 or 2 x 4 clusters whose pairs share the tile of B^T, each CTA
     loading a slice of it and multicasting it to the others
     (nvjet_hss_128x128_64x9_2x2 and _2x4): 2048^3 14.18 us against 14.21,
     3072x1280x2048 13.79 against 14.24. The wider cluster is taken when it
     needs no more waves: fewer of them fit at once.
   The rest keep the configurations CUTLASS's example transcribed to, faster
   than cuBLAS there too: the pair on 128 x 128 tiles, depth 8 -- 1536^3 7520
   ns against 8128. *)
let choose ~m ~n ~k =
  let tiles = m / 128 * (n / 128) in
  let pair_fits = m mod 256 = 0 && n mod 128 = 0 && (tiles <= sms || k / 64 mod 8 = 0) in
  let swapped_fits = n mod 256 = 0 && m mod 64 = 0 && k mod 64 = 0 && (m + 255) / 256 * (n / 128) >= sms in
  if swapped_fits && n mod 512 = 0 && m mod 256 = 0 && min m (min n k) >= 8192
  then swapped ~tile_m:256 ~tile_n:256 ~depth:4 ~clc:true ~ask_ahead:true ()
  else if swapped_fits
  then swapped ~tile_m:192 ~tile_n:128 ~depth:7 ~clc:(k >= 4096) ~ask_ahead:false ()
  else if 2 * tiles <= sms && n mod 128 = 0 && m mod 128 = 0 && k mod 64 = 0
  then swapped ~tile_m:128 ~tile_n:64 ~depth:13 ~clc:false ~ask_ahead:true ()
  else if
    let waves cn = if m mod (128 * cn) = 0 then Some ((tiles / (2 * cn) + resident_clusters (2 * cn) - 1) / resident_clusters (2 * cn)) else None in
    tiles > sms && n mod 256 = 0 && k mod 64 = 0 && waves 2 <> None
  then
    let waves cn = if m mod (128 * cn) = 0 then (tiles / (2 * cn) + resident_clusters (2 * cn) - 1) / resident_clusters (2 * cn) else max_int in
    swapped ~cluster_n:(if waves 4 <= waves 2 then 4 else 2) ~tile_m:128 ~tile_n:128 ~depth:8 ~clc:true ~ask_ahead:false ()
  else if min m (min n k) < 12288 && pair_fits
  then old_config ~tile_n:128 ~depth:8 ~cluster:2 ~pair:true
  else old_config ~tile_n:(choose_tile_n ~m ~n ~tile_m:128) ~depth:4 ~cluster:1 ~pair:false

let gemm ?(tile_m = 128) ?(tile_n = 128) ?(tile_k = 64) ?bufs ?(cluster = 1) ?(cluster_n = 1) ?(pair = false)
    ?(swap = false) ?(clc = false) ?(clc_slots = 1) ?(epi_rows = 8) ?(ask_ahead = false) ~m ~n ~k ~depth () =
  (* One instruction per 16 columns of K: M rows over the CTAs it spans, N the
     accumulator's columns. [pair] asks for the CTA-pair form. [swap] makes the
     MMA's A operand the tile of B^T, as cuBLAS's nvjet kernels do: the
     accumulator then holds the output tile transposed, its lanes running
     along the output's columns, and a CTA's tile_m x tile_n output is the
     atom's N x (M / CTAs). *)
  let ctas = if pair then 2 else 1 in
  (* The MMA covers its rows with as many atoms as it takes: an atom spans at
     most 128 rows a CTA (256 over a pair), and a taller tile stacks blocks of
     them along the rows, as nvjet's 256 x 256 tile does. *)
  let rows_needed, atom_n = if swap then tile_n * ctas, tile_m else tile_m * ctas, tile_n in
  let atom_m = min rows_needed (128 * ctas) in
  if rows_needed mod atom_m <> 0 then failwith "gemm: the MMA's rows are not whole atoms";
  let reps = rows_needed / atom_m in
  let atom = Atom.umma ~ab:F16 ~acc:F32 ~m:atom_m ~n:atom_n ~ctas ~a_major:K_major ~b_major:K_major ~a_src:Smem_desc in
  let a_tile, b_tile = if swap then "sb", "sa" else "sa", "sb" in
  (* each CTA stages the rows of A and of B the atom gives it *)
  let rows_of l = snd (Atom.cta_rows l ~cols:(Atom.umma_k atom) ~v:0) in
  (* the A operand holds each block's rows, one after the other *)
  let rows_of_a () = reps * rows_of (Atom.umma_a atom) in
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
      [ { sname = "sa"; sdtype = F16; srows = (if swap then rows_of (Atom.umma_b atom) else rows_of_a ()); scols = tile_k; ring = Stages }
      ; { sname = "sb"; sdtype = F16; srows = (if swap then rows_of_a () else rows_of (Atom.umma_b atom)); scols = tile_k; ring = Stages }
        (* one block of the output per warp, two deep so a block is written
           while the copy engine still reads the previous one: 32 rows by 32
           columns, or, with the accumulator transposed, 8 rows by the 32
           columns of the warp's lanes, as nvjet stages it *)
      ; { sname = "sc"; sdtype = F32; srows = (if swap then epi_rows else 32); scols = 32; ring = Per_warp 2 }
      ]
  ; depth
  ; tmem =
      [ { tname = "acc"
        ; trows = snd (Atom.cta_rows (Atom.umma_c atom) ~cols:atom.n ~v:0)
        ; tcols = atom.n
        ; reps
        ; (* Two accumulators let the epilogue of one tile run while the
             mainloop of the next fills the other; two 256-wide ones fill
             tensor memory exactly. A CTA with one tile has no next tile, and
             the second allocation is only cost: measured, 972 against 889 at
             2048 cubed. *)
          bufs =
            (match bufs with
             | Some b -> b
             | None -> if 2 * Atom.tmem_columns (reps * Atom.tmem_acc_columns atom) <= 512 && (m + tile_m - 1) / tile_m * ((n + tile_n - 1) / tile_n) > sms then 2 else 1)
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
    (* the cluster and the two-CTA MMA are the caller's choice; [choose] is
       the one the measurements favour *)
  ; cluster
  ; cluster_n
  ; tiles = (if clc then Clc clc_slots else Stride)
  ; ask_ahead
  ; tile_m; tile_n; tile_k; k_total = k; tile_m_count = (m + tile_m - 1) / tile_m
  ; tile_n_count = (n + tile_n - 1) / tile_n
  ; body =
      [ Role ([ 0 ], [ Kloop [ Wait "empty"; Tma { dst = "sa"; src = "a"; rows = Tile_m; pipe = "full" }; Tma { dst = "sb"; src = "bt"; rows = Tile_n; pipe = "full" } ] ])
      ; Role
          ( [ 1 ]
          , [ Wait "free"; Kloop [ Wait "full"; Mma { atom; d = "acc"; a = a_tile; b = b_tile }; Commit "empty" ]; Commit "ready" ] )
      ; Role ([ 4; 5; 6; 7 ], [ Wait "ready"; Store { dst = "c"; src = "acc"; via = "sc"; release = Some "free" } ])
      ]
      @ if clc then [ Role ([ 2 ], [ Schedule ]) ] else []
  }

(* the kernel a configuration is *)
let of_config (c : config) ~m ~n ~k =
  gemm ~tile_m:c.c_tile_m ~tile_n:c.c_tile_n ~cluster:c.c_cluster ~cluster_n:c.c_cluster_n ~pair:c.c_pair ~swap:c.c_swap ~clc:c.c_clc
    ~ask_ahead:c.c_ask_ahead ~m ~n ~k
    ~depth:c.c_depth ()

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

(* the kernel's MMA instruction; a kernel issues one kind *)
let mma_atom (k : kernel) =
  let rec walk acc = function
    | Mma { atom; _ } -> atom :: acc
    | Kloop b | Role (_, b) -> List.fold_left walk acc b
    | _ -> acc
  in
  match List.sort_uniq compare (List.fold_left walk [] k.body) with
  | [] -> None
  | [ a ] -> Some a
  | _ -> failwith "a kernel issues one kind of MMA"

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
  let atom = Option.get (mma_atom g) in
  only_used
  { g with
    name = Printf.sprintf "pmma_%d_%d_%d_s%d" m n k depth
  ; body =
      [ Role ([ 0 ], [ Kloop [ Wait "empty"; Tma { dst = "sa"; src = "a"; rows = Tile_m; pipe = "full" }; Tma { dst = "sb"; src = "bt"; rows = Tile_n; pipe = "full" } ] ])
      ; Role ([ 1 ], [ Kloop [ Wait "full"; Mma { atom; d = "acc"; a = "sa"; b = "sb" }; Commit "empty" ]; Commit "ready"; Wait "ready" ]) ] }

let epi_probe ~m ~n ~k =
  let g = gemm ~m ~n ~k ~depth:1 () in
  only_used
  { g with
    name = Printf.sprintf "pepi_%d_%d_%d_s1" m n k
  ; body = [ Role ([ 1 ], [ Commit "ready"; Wait "free" ]); Role ([ 4; 5; 6; 7 ], [ Wait "ready"; Store { dst = "c"; src = "acc"; via = "sc"; release = Some "free" } ]) ] }

let dtype_string = Atom.elt_string
let coord_string = function Tile_m -> "tile_m" | Tile_n -> "tile_n"

let rec stmt_string ind = function
  | Tma { dst; src; rows; pipe } -> Printf.sprintf "%s%s[stage] <- tma %s[%s rows, k tile]  -> %s" ind dst src (coord_string rows) pipe
  | Wait p -> ind ^ "wait " ^ p
  | Mma { atom; d; a; b } -> Printf.sprintf "%s%s += %s[stage] . %s[stage]^T  by %s" ind d a b (Atom.umma_string atom)
  | Commit p -> ind ^ "commit " ^ p
  | Signal p -> ind ^ "signal " ^ p
  | Schedule -> ind ^ "take the tiles of unlaunched clusters, for every role of the cluster"
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
     ; Printf.sprintf "  tile %dx%d, k tile %d, ring depth %d, %d warps, cluster %dx%d, %s" k.tile_m k.tile_n k.tile_k
         k.depth k.nwarps k.cluster k.cluster_n
         (match k.tiles with Stride -> "a grid of one CTA per multiprocessor" | Clc n -> Printf.sprintf "cluster launch control, %d slots" n)
       ^ if k.ask_ahead then ", the MMA asks a stage ahead" else "" ]
     @ List.map
         (fun (s : stile) ->
           Printf.sprintf "  smem %s : %s[%d,%d] x %s" s.sname (dtype_string s.sdtype) s.srows s.scols
             (match s.ring with Stages -> "depth" | Per_warp n -> Printf.sprintf "%d per warp" n))
         k.smem
     @ List.map (fun (t : ttile) -> Printf.sprintf "  tmem %s : f32[%d,%d] x %d blocks x %d buffers" t.tname t.trows t.tcols t.reps t.bufs) k.tmem
     @ List.map (fun (p : pipe) -> Printf.sprintf "  pipe %s%s, %d arrival%s%s" p.pname (if p.per_stage then "[stage]" else if p.per_buffer then "[buffer]" else "") p.arrivals (if p.arrivals > 1 then "s" else "") (if p.free_at_start then ", free at start" else "")) k.pipes
     @ List.map (stmt_string "  ") k.body)
