(* The formulas of the usage table (paper, Section 6), built exactly as
   printed. The paper writes g ∘ f for "f first, then g"; in code that is
   [Layout.compose f g]. So the paper's  A ∘ F  is  [compose F A]. *)

open Layouts

let check name b = if not b then failwith ("usage table: " ^ name)

(* fix a whole coordinate *)
let rec fix (c : Coord.t) : Coord.partial =
  match c with
  | Coord.Idx i -> Coord.At i
  | Coord.Tuple cs -> Coord.Parts (List.map fix cs)

(* A: an (8,6) tile in storage with leading dimension 7 *)
let a_lin : Linear.t = Group [ Axis { size = 8; stride = 7 }; Axis { size = 6; stride = 1 } ]
let a : (Space.logical, Space.physical) Layout.t = Layout.storage a_lin
let a_at i j = Linear.eval a_lin (Coord.Tuple [ Idx i; Idx j ])

(* local_tile(A, S, b) = divide(A, S)|_{rest = b} *)
let () =
  let tiled = Layout.divide ~by:(Product [ Bound 4; Bound 3 ]) a in
  for bi = 0 to 1 do
    for bj = 0 to 1 do
      let sl =
        Restricted.restrict ~at:(Coord.Parts [ Free; fix (Coord.Tuple [ Idx bi; Idx bj ]) ]) tiled
      in
      for i = 0 to 3 do
        for j = 0 to 2 do
          let got =
            Restricted.offset
              sl
              (Coord.Tuple [ Tuple [ Idx i; Idx j ]; Tuple [ Idx 0; Idx 0 ] ])
          in
          check "local_tile" (got = a_at ((4 * bi) + i) ((3 * bj) + j))
        done
      done
    done
  done

(* local_partition(A, T, t) = divide(A, S_T)|_{tile = inverse(T)(t)}:
   thread t takes, in every tile, the position c with T(c) = t *)
let () =
  let t_lin : Linear.t = Group [ Axis { size = 4; stride = 1 }; Axis { size = 3; stride = 4 } ] in
  let s_t = Linear.shape t_lin in
  let tiled = Layout.divide ~by:s_t a in
  let inv = Linear.inverse t_lin in
  for t = 0 to 11 do
    let c = Coord.unflatten s_t (Linear.eval inv (Coord.unflatten (Linear.shape inv) t)) in
    check "inverse(T)(t)" (Linear.eval t_lin c = t);
    let ci, cj =
      match c with
      | Coord.Tuple [ Idx ci; Idx cj ] -> ci, cj
      | _ -> assert false
    in
    let sl = Restricted.restrict ~at:(Coord.Parts [ fix c; Free ]) tiled in
    for bi = 0 to 1 do
      for bj = 0 to 1 do
        let got =
          Restricted.offset
            sl
            (Coord.Tuple [ Tuple [ Idx 0; Idx 0 ]; Tuple [ Idx bi; Idx bj ] ])
        in
        check "local_partition" (got = a_at ((4 * bi) + ci) ((3 * bj) + cj))
      done
    done
  done

(* partition_C: (A ∘ F)|_{thread = t}, F a thread-value -> logical map *)
let () =
  let f_lin : Linear.t = Group [ Axis { size = 8; stride = 1 }; Axis { size = 6; stride = 8 } ] in
  let f : (Space.thread_value, Space.logical) Layout.t = Layout.of_linear f_lin in
  let af = Layout.compose f a in
  for t = 0 to 7 do
    let sl = Restricted.restrict ~at:(Coord.Parts [ At t; Free ]) af in
    for v = 0 to 5 do
      let e = Linear.eval f_lin (Coord.Tuple [ Idx t; Idx v ]) in
      let got = Restricted.offset sl (Coord.Tuple [ Idx 0; Idx v ]) in
      check "partition_C" (got = Linear.eval a_lin (Coord.unflatten (Linear.shape a_lin) e))
    done
  done

(* TiledCopy: divide(A, (1,v)) ∘ interleave(v:1, T) *)
let () =
  let g : (Space.logical, Space.physical) Layout.t =
    Layout.storage (Group [ Axis { size = 8; stride = 40 }; Axis { size = 32; stride = 1 } ])
  in
  let tiled_v = Layout.divide ~by:(Product [ Bound 1; Bound 8 ]) g in
  let vec : (Space.thread_value, Space.logical) Layout.t = Layout.of_linear (Axis { size = 8; stride = 1 }) in
  let tv = Layout.interleave ~by:(Axis { size = 32; stride = 1 }) vec in
  let copy = Layout.compose tv tiled_v in
  for l = 0 to 31 do
    let a0 = Layout.offset copy (Coord.Tuple [ Idx l; Idx 0 ]) in
    for e = 1 to 7 do
      check "TiledCopy: vector contiguous" (Layout.offset copy (Coord.Tuple [ Idx l; Idx e ]) = a0 + e)
    done;
    if l mod 4 < 3
    then check "TiledCopy: lanes consecutive" (Layout.offset copy (Coord.Tuple [ Idx (l + 1); Idx 0 ]) = a0 + 8)
  done

(* TiledMMA: divide(A, S_F) ∘ interleave(F, W), on an (8,4) tile: four
   (4,2) mma tiles for the (2,2) warp grid *)
let () =
  let a84_lin : Linear.t = Group [ Axis { size = 8; stride = 5 }; Axis { size = 4; stride = 1 } ] in
  let a84 : (Space.logical, Space.physical) Layout.t = Layout.storage a84_lin in
  let a_at i j = Linear.eval a84_lin (Coord.Tuple [ Idx i; Idx j ]) in
  let f_lin : Linear.t = Group [ Axis { size = 4; stride = 1 }; Axis { size = 2; stride = 4 } ] in
  let w_lin : Linear.t = Group [ Axis { size = 2; stride = 2 }; Axis { size = 2; stride = 1 } ] in
  let tiled = Layout.divide ~by:(Product [ Bound 4; Bound 2 ]) a84 in
  let f : (Space.thread_value, Space.logical) Layout.t = Layout.of_linear f_lin in
  let mma = Layout.compose (Layout.interleave ~by:w_lin f) tiled in
  for w0 = 0 to 1 do
    for w1 = 0 to 1 do
      let tile = Linear.eval w_lin (Coord.Tuple [ Idx w0; Idx w1 ]) in
      let ti, tj = tile / 2, tile mod 2 in
      for t = 0 to 3 do
        for v = 0 to 1 do
          let e = Linear.eval f_lin (Coord.Tuple [ Idx t; Idx v ]) in
          let i, j = e / 2, e mod 2 in
          let got =
            Layout.offset mma (Coord.Tuple [ Tuple [ Idx w0; Idx w1 ]; Tuple [ Idx t; Idx v ] ])
          in
          check "TiledMMA" (got = a_at ((4 * ti) + i) ((2 * tj) + j))
        done
      done
    done
  done

(* k-stage buffer: repeat(L, k:1) *)
let () =
  let staged = Layout.repeat ~by:(Axis { size = 3; stride = 1 }) a in
  let cosz = Linear.cosize a_lin in
  for s = 0 to 2 do
    for i = 0 to 7 do
      for j = 0 to 5 do
        check "k-stage"
          (Layout.offset staged (Coord.Tuple [ Idx s; Tuple [ Idx i; Idx j ] ]) = (s * cosz) + a_at i j)
      done
    done
  done

(* products, for A = 4:1 and B = 2:1 (dense bijections):
   A ⊗ B = (A, complement(A, 8) ∘ B) = (4:1, 2:4)  -> ours (2,4):(4,1) = repeat(A, B)
   raked_product(A, B) = A ⊗ B zipped copy-first = ((2,4):(4,1)) -> ours (4,2):(1,4)
   B ⊗ A = (B, complement(B, 8) ∘ A) = (2:1, 4:2)  -> ours (4,2):(2,1), = interleave(A, B) with groups exchanged *)
let () =
  let a4 : Linear.t = Axis { size = 4; stride = 1 } and b2 : Linear.t = Axis { size = 2; stride = 1 } in
  let same (x : Linear.t) (y : Linear.t) =
    let sx = Linear.shape x and sy = Linear.shape y in
    Shape.size sx = Shape.size sy
    && List.for_all
         (fun i -> Linear.eval x (Coord.unflatten sx i) = Linear.eval y (Coord.unflatten sy i))
         (List.init (Shape.size sx) (fun i -> i))
  in
  let repeat = Linear.repeat ~by:b2 a4 in
  check "A⊗B = repeat" (same repeat (Group [ Axis { size = 2; stride = 4 }; Axis { size = 4; stride = 1 } ]));
  let raked : Linear.t = Group [ Axis { size = 4; stride = 1 }; Axis { size = 2; stride = 4 } ] in
  for e = 0 to 3 do
    for c = 0 to 1 do
      check "raked = repeat, groups exchanged"
        (Linear.eval raked (Coord.Tuple [ Idx e; Idx c ]) = Linear.eval repeat (Coord.Tuple [ Idx c; Idx e ]))
    done
  done;
  let b_times_a : Linear.t = Group [ Axis { size = 4; stride = 2 }; Axis { size = 2; stride = 1 } ] in
  let inter = Linear.interleave ~by:b2 a4 in
  for e = 0 to 3 do
    for c = 0 to 1 do
      check "B⊗A = interleave, groups exchanged"
        (Linear.eval b_times_a (Coord.Tuple [ Idx e; Idx c ]) = Linear.eval inter (Coord.Tuple [ Idx c; Idx e ]))
    done
  done

(* CuTe's product for a block with gaps: A ⊗ B = divide(canonical(R), S) ∘ repeat(B, canonical(S_A)),
   for A = (2,2):(4,1), M = 24, R = (3,2,2,2,1), S = (1,2,1,2,1), and B = (3,2):(1,3) a
   non-identity dense bijection onto 6. CuTe's A*_24 = (2,3):(2,8) is k ↦ 8⌊k/2⌋ + 2(k mod 2). *)
let () =
  let a : Linear.t = Group [ Axis { size = 2; stride = 4 }; Axis { size = 2; stride = 1 } ] in
  let b : Linear.t = Group [ Axis { size = 3; stride = 1 }; Axis { size = 2; stride = 3 } ] in
  let astar k = (8 * (k / 2)) + (2 * (k mod 2)) in
  let pair =
    Linear.divide
      ~by:(Product [ Bound 1; Bound 2; Bound 1; Bound 2; Bound 1 ])
      (Linear.canonical (Product [ Bound 3; Bound 2; Bound 2; Bound 2; Bound 1 ]))
  in
  let reorder = Linear.repeat ~by:(Linear.canonical (Linear.shape a)) b in
  let prod = Layout.compose (Layout.of_linear reorder) (Layout.storage pair) in
  for i = 0 to 1 do
    for j = 0 to 1 do
      for b0 = 0 to 2 do
        for b1 = 0 to 1 do
          let ours =
            Layout.offset prod (Coord.Tuple [ Tuple [ Idx i; Idx j ]; Tuple [ Idx b0; Idx b1 ] ])
          in
          let cute =
            Linear.eval a (Coord.Tuple [ Idx i; Idx j ])
            + astar (Linear.eval b (Coord.Tuple [ Idx b0; Idx b1 ]))
          in
          check "A⊗B via divide ∘ repeat" (ours = cute)
        done
      done
    done
  done;
  (* B = 6:1: divide of the (6,4) matrix alone *)
  let d = Linear.divide ~by:(Product [ Bound 2; Bound 2 ]) (Linear.canonical (Product [ Bound 6; Bound 4 ])) in
  for i = 0 to 1 do
    for j = 0 to 1 do
      for k = 0 to 5 do
        let ours = Linear.eval d (Coord.Tuple [ Tuple [ Idx i; Idx j ]; Tuple [ Idx (k / 2); Idx (k mod 2) ] ]) in
        check "A⊗(6:1) = divide(canonical((6,4)),(2,2))" (ours = Linear.eval a (Coord.Tuple [ Idx i; Idx j ]) + astar k)
      done
    done
  done


let same_fn (x : Linear.t) (y : Linear.t) =
  let sx = Linear.shape x and sy = Linear.shape y in
  Shape.size sx = Shape.size sy
  && List.for_all
       (fun i -> Linear.eval x (Coord.unflatten sx i) = Linear.eval y (Coord.unflatten sy i))
       (List.init (Shape.size sx) (fun i -> i))

(* complement(B, 24) = rest of divide(canonical(R), S), for all six documented complements.
   R is the factor shape of M (our order), S is R with the N_i kept and everything else 1.
   B and its complement are written in our convention (CuTe's mode list reversed). *)
let () =
  let cases : (string * Shape.t * Shape.t * Linear.t * Linear.t) list =
    [ ( "complement(4:1,24)=6:4", Product [ Bound 6; Bound 4; Bound 1 ], Product [ Bound 1; Bound 4; Bound 1 ]
      , Axis { size = 4; stride = 1 }, Axis { size = 6; stride = 4 } )
    ; ( "complement(6:4,24)=4:1", Product [ Bound 1; Bound 6; Bound 4 ], Product [ Bound 1; Bound 6; Bound 1 ]
      , Axis { size = 6; stride = 4 }, Axis { size = 4; stride = 1 } )
    ; ( "complement(4:2,24)=(2,3):(1,8)", Product [ Bound 3; Bound 4; Bound 2 ], Product [ Bound 1; Bound 4; Bound 1 ]
      , Axis { size = 4; stride = 2 }, Group [ Axis { size = 3; stride = 8 }; Axis { size = 2; stride = 1 } ] )
    ; ( "complement((2,4):(1,6),24)=3:2"
      , Product [ Bound 1; Bound 4; Bound 3; Bound 2; Bound 1 ], Product [ Bound 1; Bound 4; Bound 1; Bound 2; Bound 1 ]
      , Group [ Axis { size = 4; stride = 6 }; Axis { size = 2; stride = 1 } ], Axis { size = 3; stride = 2 } )
    ; ( "complement((2,2):(1,6),24)=(3,2):(2,12)"
      , Product [ Bound 2; Bound 2; Bound 3; Bound 2; Bound 1 ], Product [ Bound 1; Bound 2; Bound 1; Bound 2; Bound 1 ]
      , Group [ Axis { size = 2; stride = 6 }; Axis { size = 2; stride = 1 } ]
      , Group [ Axis { size = 2; stride = 12 }; Axis { size = 3; stride = 2 } ] )
    ; ( "complement((4,6):(1,4),24)=1:0"
      , Product [ Bound 1; Bound 6; Bound 1; Bound 4; Bound 1 ], Product [ Bound 1; Bound 6; Bound 1; Bound 4; Bound 1 ]
      , Group [ Axis { size = 6; stride = 4 }; Axis { size = 4; stride = 1 } ], Axis { size = 1; stride = 1 } )
    ]
  in
  List.iter
    (fun (name, r, s, b, bstar) ->
      match Linear.divide ~by:s (Linear.canonical r) with
      | Group [ tile; rest ] ->
        check (name ^ ": tile") (same_fn tile b);
        check (name ^ ": rest") (same_fn rest bstar)
      | _ -> check (name ^ ": shape") false)
    cases

(* Swizzle<B,M,S> of CuTe, offset ^ ((offset & (mask << (M+S))) >> S), is our {bits=B; src=M+S; dst=M} *)
let () =
  List.iter
    (fun (b, m, s) ->
      let ours : Swizzle.t = { bits = b; src = m + s; dst = m } in
      for x = 0 to 4095 do
        let cute = x lxor (((x lsr (m + s)) land ((1 lsl b) - 1)) lsl m) in
        check "Swizzle<B,M,S>" (Swizzle.eval ours x = cute)
      done)
    [ 3, 4, 3; 2, 4, 3; 1, 4, 3; 3, 0, 3; 2, 3, 3 ]

(* logical_divide with a shape tiler: divide(A, S) = A ∘ divide(canonical(S_A), S) *)
let () =
  let a2 : Linear.t = Group [ Axis { size = 8; stride = 7 }; Axis { size = 6; stride = 1 } ] in
  let s2 : Shape.t = Product [ Bound 4; Bound 3 ] in
  let lhs = Linear.divide ~by:s2 a2 in
  let rhs =
    Layout.compose
      (Layout.of_linear (Linear.divide ~by:s2 (Linear.canonical (Linear.shape a2))))
      (Layout.storage a2)
  in
  let sl = Linear.shape lhs in
  check "divide(A,S) = A o divide(canonical(S_A),S)"
    (Shape.size sl = Shape.size (Layout.shape rhs)
     && List.for_all
          (fun i ->
            Linear.eval lhs (Coord.unflatten sl i)
            = Layout.offset rhs (Coord.unflatten (Layout.shape rhs) i))
          (List.init (Shape.size sl) (fun i -> i)))


(* logical_divide with a SHAPE tiler, by CuTe's per-mode definition: mode i of A composed with
   (k_i:1, complement(k_i:1, n_i)) = (k_i:1, (n_i/k_i):k_i), then zipped as ((tiles),(rests)).
   A = (8,6):(7,1), tiler (4,3): mode 0: 8:7 o (4:1, 2:4) = (4,2):(7,28); mode 1: 6:1 o (3:1, 2:3) = (3,2):(1,3);
   zipped_divide = ((4,3),(2,2)):((7,1),(28,3)) — must equal our divide(A, (4,3)) as a function. *)
let () =
  let a2 : Linear.t = Group [ Axis { size = 8; stride = 7 }; Axis { size = 6; stride = 1 } ] in
  let per_mode (n, d) k : Linear.t * Linear.t =
    (* A_i = n:d composed with the pair (k:1, (n/k):k): tile k:d, rest (n/k):(k d) *)
    let pair : Linear.t = Group [ Axis { size = k; stride = 1 }; Axis { size = n / k; stride = k } ] in
    let comp = Layout.compose (Layout.of_linear pair) (Layout.storage (Axis { size = n; stride = d })) in
    let tile_stride = Layout.offset comp (Coord.Tuple [ Idx 1; Idx 0 ]) in
    let rest_stride = Layout.offset comp (Coord.Tuple [ Idx 0; Idx 1 ]) in
    (* the composite is affine in (t, b): check, then read the two strides *)
    for tt = 0 to k - 1 do
      for b = 0 to (n / k) - 1 do
        check "per-mode composite affine"
          (Layout.offset comp (Coord.Tuple [ Idx tt; Idx b ]) = (tt * tile_stride) + (b * rest_stride))
      done
    done;
    Axis { size = k; stride = tile_stride }, Axis { size = n / k; stride = rest_stride }
  in
  let t0, r0 = per_mode (8, 7) 4 and t1, r1 = per_mode (6, 1) 3 in
  let zipped : Linear.t = Group [ Group [ t0; t1 ]; Group [ r0; r1 ] ] in
  check "zipped_divide by CuTe's per-mode definition = divide(A, (4,3))"
    (same_fn zipped (Linear.divide ~by:(Product [ Bound 4; Bound 3 ]) a2))

let () = print_endline "usage table formulas built as printed: passed"
