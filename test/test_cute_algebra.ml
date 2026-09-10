(* Verification of CuTe's CENTRAL ALGEBRA against ours, on NVIDIA's own
   worked examples (docs/cpp/cute/02_layout_algebra.html). This is the
   factorization claim executed: their composition / complement /
   logical_divide reproduce under our ops.

   Convention translation (mechanical, applies to inputs AND expected
   outputs): a CuTe layout (s0,s1,..):(d0,d1,..) linearizes col-major
   (first mode fastest); ours row-major (last fastest). So a CuTe
   layout becomes our Group with the modes REVERSED (recursively), and
   the two then agree as functions on the same integer domain.

   CuTe composition(A, B) applies B first — it is our compose with
   f = B, g = A. *)

open Layouts
module Layout = Test_util.Checked_layout

(* function equality on the shared integer domain *)
let same_function (a : Linear.t) (b : Linear.t) =
  let sa = Linear.shape a
  and sb = Linear.shape b in
  Shape.size sa = Shape.size sb
  && List.for_all
       (fun i ->
         Linear.eval a (Coord.unflatten sa i) = Linear.eval b (Coord.unflatten sb i))
       (List.init (Shape.size sa) (fun i -> i))

let dense l ~size = Layout.is_bijection_onto (Layout.of_linear l) ~size

(* ---- composition: all three documented examples ----
   Composition keeps the operand pair; we verify the composite FUNCTION
   equals CuTe's documented result, over the whole domain. CuTe's
   composition(A, B) applies B first = our compose with f = B, g = A. *)

let compose_equals ~a ~b ~expected =
  let comp = Layout.compose (Layout.of_linear b) (Layout.of_linear a) in
  let se = Linear.shape expected in
  Shape.size (Layout.shape comp) = Shape.size se
  && List.for_all
       (fun i ->
         Layout.offset comp (Coord.unflatten (Layout.shape comp) i)
         = Linear.eval expected (Coord.unflatten se i))
       (List.init (Shape.size se) (fun i -> i))

let () =
  (* composition((6,2):(8,2), (4,3):(3,1)) = ((2,2),3):((24,2),8) *)
  assert (
    compose_equals
      ~a:(Group [ Axis { size = 2; stride = 2 }; Axis { size = 6; stride = 8 } ])
      ~b:(Group [ Axis { size = 3; stride = 1 }; Axis { size = 4; stride = 3 } ])
      ~expected:
        (Group
           [ Axis { size = 3; stride = 8 }
           ; Group [ Axis { size = 2; stride = 2 }; Axis { size = 2; stride = 24 } ]
           ]))

let () =
  (* composition(20:2, (5,4):(4,1)) = (5,4):(8,2) *)
  assert (
    compose_equals
      ~a:(Axis { size = 20; stride = 2 })
      ~b:(Group [ Axis { size = 4; stride = 1 }; Axis { size = 5; stride = 4 } ])
      ~expected:(Group [ Axis { size = 4; stride = 2 }; Axis { size = 5; stride = 8 } ]))

let () =
  (* composition((10,2):(16,4), (5,4):(1,5)) = (5,(2,2)):(16,(80,4)) *)
  assert (
    compose_equals
      ~a:(Group [ Axis { size = 2; stride = 4 }; Axis { size = 10; stride = 16 } ])
      ~b:(Group [ Axis { size = 4; stride = 5 }; Axis { size = 5; stride = 1 } ])
      ~expected:
        (Group
           [ Group [ Axis { size = 2; stride = 4 }; Axis { size = 2; stride = 80 } ]
           ; Axis { size = 5; stride = 16 }
           ]))

(* ---- complement: all six documented examples ---- *)

(* In our algebra the complement is never a standalone op: it is the
   REST component that [divide] carries by construction, and its
   defining property — (B, complement(B, M)) is a bijection onto
   [0, M) — is decided by our density checker. Both are exercised. *)

let () =
  (* complement(4:1, 24) = 6:4 and complement(6:4, 24) = 4:1 —
     both witnessed by ONE divide: tile and rest are each other's
     complements *)
  (match Linear.divide ~by:(Bound 4) (Linear.canonical (Bound 24)) with
   | Group [ tile; rest ] ->
     assert (same_function tile (Axis { size = 4; stride = 1 }));
     assert (same_function rest (Axis { size = 6; stride = 4 }))
   | _ -> assert false);
  (* complement(4:2, 24) = (2,3):(1,8) — produced by dividing the
     (12,2) reshape of 24: the tile comes out as 4:2 *)
  (match
     Linear.divide
       ~by:(Product [ Bound 4; Bound 1 ])
       (Linear.canonical (Product [ Bound 12; Bound 2 ]))
   with
   | Group [ tile; rest ] ->
     assert (same_function tile (Axis { size = 4; stride = 2 }));
     assert (
       same_function rest (Group [ Axis { size = 3; stride = 8 }; Axis { size = 2; stride = 1 } ]))
   | _ -> assert false);
  (* the defining property, for every documented pair: (B, Bc) with
     Bc = their complement must be dense onto [0,24). The CuTe pair
     (B, Bc) is col-major, i.e. our Group [Bc; B]. *)
  let pairs : Linear.t list =
    [ Group [ Axis { size = 6; stride = 4 }; Axis { size = 4; stride = 1 } ]
    ; Group
        [ Group [ Axis { size = 3; stride = 8 }; Axis { size = 2; stride = 1 } ]
        ; Axis { size = 4; stride = 2 }
        ]
    ; (* complement((2,4):(1,6), 24) = 3:2 *)
      Group
        [ Axis { size = 3; stride = 2 }
        ; Group [ Axis { size = 4; stride = 6 }; Axis { size = 2; stride = 1 } ]
        ]
    ; (* complement((2,2):(1,6), 24) = (3,2):(2,12) *)
      Group
        [ Group [ Axis { size = 2; stride = 12 }; Axis { size = 3; stride = 2 } ]
        ; Group [ Axis { size = 2; stride = 6 }; Axis { size = 2; stride = 1 } ]
        ]
    ]
  in
  List.iter (fun p -> assert (dense p ~size:24)) pairs;
  (* complement((4,6):(1,4), 24) = 1:0 — i.e. that layout is already a
     bijection onto [0,24), nothing to complement *)
  assert (dense (Group [ Axis { size = 6; stride = 4 }; Axis { size = 4; stride = 1 } ]) ~size:24)

(* ---- logical_divide, with a STRIDED tiler ---- *)

let () =
  (* logical_divide((4,2,3):(2,1,8), 4:2) = ((2,2),(2,3)):((4,1),(2,8)).
     Their divide = composition(A, (B, complement(B, 24))) — with the
     completed tiler it is exactly our compose, the factorization claim
     on their own example. *)
  let a : Linear.t =
    Group
      [ Axis { size = 3; stride = 8 }; Axis { size = 2; stride = 1 }; Axis { size = 4; stride = 2 } ]
  in
  let b_completed : Linear.t =
    Group
      [ Group [ Axis { size = 3; stride = 8 }; Axis { size = 2; stride = 1 } ]
      ; Axis { size = 4; stride = 2 }
      ]
  in
  let expected : Linear.t =
    Group
      [ Group [ Axis { size = 3; stride = 8 }; Axis { size = 2; stride = 2 } ]
      ; Group [ Axis { size = 2; stride = 1 }; Axis { size = 2; stride = 4 } ]
      ]
  in
  assert (compose_equals ~a ~b:b_completed ~expected)

(* ---- logical_product ---- *)

let () =
  (* logical_product((2,2):(4,1), 6:1) = ((2,2),(2,3)):((4,1),(2,8)).
     Their product on a HOLEY tile (cosize 6 > size 4) interleaves the
     copies INTO the holes via complement. We verify their result is
     what their formula says — (A, complement(A,24)) assembled, dense —
     and note the deliberate divergence: OUR repeat preserves holes
     (padding is padding); their gap-filling arrangement is expressible
     as data, not produced by our repeat. *)
  let their_result : Linear.t =
    Group
      [ Group [ Axis { size = 3; stride = 8 }; Axis { size = 2; stride = 2 } ]
      ; Group [ Axis { size = 2; stride = 1 }; Axis { size = 2; stride = 4 } ]
      ]
  in
  assert (dense their_result ~size:24);
  (* our repeat of the same holey tile: copies at the footprint, holes
     preserved — a DIFFERENT function, injective, not dense *)
  let ours =
    Linear.repeat
      ~by:(Axis { size = 6; stride = 1 })
      (Group [ Axis { size = 2; stride = 1 }; Axis { size = 2; stride = 4 } ])
  in
  assert (Layout.is_injective (Layout.of_linear ours));
  assert (not (dense ours ~size:36))
(* The second documented product example is omitted: the value we
   fetched for it, ((2,2),(2,4)):((4,1),(2,2)), is not injective as
   printed (two modes with stride 2 overlap) — needs checking against
   the primary source before it can serve as an expected value. *)

let () = print_endline "cute central algebra verification passed"
let () = Test_util.report "cute algebra"
