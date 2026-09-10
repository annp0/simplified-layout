open Layouts
module Layout = Test_util.Checked_layout

(* Row-major 8x16: offset (r, c) = r * 16 + c *)
let row_major : Linear.t =
  Group [ Axis { size = 8; stride = 16 }; Axis { size = 16; stride = 1 } ]

(* Same 8x16 tile, column-major: offset (r, c) = r + c * 8 *)
let col_major : Linear.t =
  Group [ Axis { size = 8; stride = 1 }; Axis { size = 16; stride = 8 } ]

(* The partitioned-row case: the 8 rows split into 2 groups of 4,
   row = hi * 4 + lo, still addressing the same row-major storage.
   Coordinate ((hi, lo), col). *)
let partitioned_rows : Linear.t =
  Group
    [ Group [ Axis { size = 2; stride = 64 }; Axis { size = 4; stride = 16 } ]
    ; Axis { size = 16; stride = 1 }
    ]

let logical_8x16 : Shape.t = Product [ Bound 8; Bound 16 ]

let () =
  (* Shapes and sizes. *)
  assert (Shape.size (Linear.shape row_major) = 128);
  assert (Shape.size (Linear.shape partitioned_rows) = 128);
  (* fits: structure and bounds both checked. *)
  assert (Coord.(fits (Tuple [ Idx 2; Idx 5 ]) (Linear.shape row_major)));
  assert (not Coord.(fits (Tuple [ Idx 8; Idx 5 ]) (Linear.shape row_major)));
  assert (not Coord.(fits (Idx 3) (Linear.shape row_major)));
  (* Same logical element (2, 5), different physical offsets. *)
  assert (Linear.eval row_major Coord.(Tuple [ Idx 2; Idx 5 ]) = 37);
  assert (Linear.eval col_major Coord.(Tuple [ Idx 2; Idx 5 ]) = 42);
  (* ((1, 0), 7) is row 1*4+0 = 4, col 7 -> 4*16+7 = 71. *)
  assert (Linear.eval partitioned_rows Coord.(Tuple [ Tuple [ Idx 1; Idx 0 ]; Idx 7 ]) = 71)

(* Roles are phantom types: the same data, different layout types. *)
let storage : (Space.logical, Space.physical) Layout.t = Layout.storage row_major
let tv : (Space.thread_value, Space.logical) Layout.t = Layout.of_linear row_major
let storage_offset (l : (Space.logical, Space.physical) Layout.t) c = Layout.offset l c

let () =
  assert (storage_offset storage Coord.(Tuple [ Idx 2; Idx 5 ]) = 37);
  (* This line is the whole point of the phantom parameters; uncomment
     it and the build fails with a type error, not a runtime bug:

       let _ = storage_offset tv Coord.(Tuple [ Idx 2; Idx 5 ])
  *)
  ignore tv

(* ---- swizzle: generatable non-linear maps, as data ---- *)

let bank_swizzle : Swizzle.t = { bits = 3; src = 4; dst = 0 }

let () =
  (* XOR the row bits into the low column bits: row 0 untouched, row 2
     XORs its low offset bits with 2. *)
  let swizzled = Layout.with_swizzle (Layout.storage row_major) bank_swizzle in
  assert (Layout.offset swizzled Coord.(Tuple [ Idx 0; Idx 5 ]) = 5);
  assert (Layout.offset swizzled Coord.(Tuple [ Idx 2; Idx 5 ]) = 37 lxor 2);
  (* Still a bijection on the tile: no strides can represent it, but the
     data (linear + swizzle) fully describes it. *)
  assert (Layout.is_bijection_onto swizzled ~size:128)

(* ---- density: canonical and unflatten ---- *)

let () =
  let can = Linear.canonical logical_8x16 in
  assert (Linear.compare can row_major = 0);
  assert (Layout.is_bijection_onto (Layout.of_linear can) ~size:128);
  for i = 0 to 127 do
    assert (Linear.eval can (Coord.unflatten logical_8x16 i) = i)
  done

(* ---- composition: the pair, evaluated through the middle shape ---- *)

(* TV layout: 32 threads x 4 values -> logical (8, 16).
   Thread (r, cg) holds value v at logical (r, cg*4 + v); the strides
   live in the row-major linearization of (8, 16). *)
let tv_linear : Linear.t =
  Group
    [ Group [ Axis { size = 8; stride = 16 }; Axis { size = 4; stride = 4 } ]
    ; Axis { size = 4; stride = 1 }
    ]

let () =
  let tv : (Space.thread_value, Space.logical) Layout.t = Layout.of_linear tv_linear in
  let storage : (Space.logical, Space.physical) Layout.t = Layout.storage col_major in
  let addr = Layout.compose tv storage in
  (* thread (1, 2), value 3 -> logical (1, 11) -> col-major 1 + 11*8 = 89 *)
  assert (Layout.offset addr Coord.(Tuple [ Tuple [ Idx 1; Idx 2 ]; Idx 3 ]) = 89);
  (* agreement with the semantic definition, over the whole domain *)
  List.iter
    (fun c ->
      assert (
        Layout.offset addr c
        = Layout.offset storage (Coord.unflatten logical_8x16 (Layout.offset tv c))))
    (Coord.enumerate (Layout.shape tv));
  assert (Layout.is_bijection_onto addr ~size:128)

let () =
  (* shape refinement: the flat 128 view of the tile, through col-major
     storage, splits into (8,16):(1,8) *)
  let flat : (Space.logical, Space.logical) Layout.t =
    Layout.of_linear (Axis { size = 128; stride = 1 })
  in
  let addr = Layout.compose flat (Layout.of_linear col_major) in
  (* flat index 17 is tile (1,1): col-major offset 1 + 8 = 9 *)
  assert (Layout.offset addr (Idx 17) = 9);
  assert (Layout.is_bijection_onto addr ~size:128)

let () =
  (* the swizzle on storage rides along untouched *)
  let storage = Layout.with_swizzle (Layout.storage col_major) bank_swizzle in
  let addr = Layout.compose (Layout.of_linear tv_linear) storage in
  assert (Layout.offset addr Coord.(Tuple [ Tuple [ Idx 1; Idx 2 ]; Idx 3 ])
          = Swizzle.eval bank_swizzle 89);
  assert (Layout.is_bijection_onto addr ~size:128)

let () =
  (* no strided form: relabel (2,3) |-> 3a+b viewed into (3,2) with
     strides (1,3). The size-3 axis lands at offsets 0,3,1 — prime,
     unsplittable, no strided form over any refinement. Dense, so it
     composes; the composite is simply the pair. *)
  let f : (Space.logical, Space.logical) Layout.t =
    Layout.of_linear (Group [ Axis { size = 2; stride = 3 }; Axis { size = 3; stride = 1 } ])
  in
  let g : (Space.logical, Space.physical) Layout.t =
    Layout.storage (Group [ Axis { size = 3; stride = 1 }; Axis { size = 2; stride = 3 } ])
  in
  assert (Layout.is_bijection_onto f ~size:6);
  let comp = Layout.compose f g in
  (* along the size-3 axis at a = 0 the addresses are 0, 3, 1 — the
     composite is a perfectly good address map, just not strided *)
  assert (Layout.offset comp Coord.(Tuple [ Idx 0; Idx 0 ]) = 0);
  assert (Layout.offset comp Coord.(Tuple [ Idx 0; Idx 1 ]) = 3);
  assert (Layout.offset comp Coord.(Tuple [ Idx 0; Idx 2 ]) = 1);
  assert (Layout.is_bijection_onto comp ~size:6)

(* ---- partition (split) stays dense ---- *)

let () =
  let can = Linear.canonical logical_8x16 in
  let split =
    match can with
    | Group [ rows; cols ] ->
      Linear.Group [ Linear.split ~by:(Product [ Bound 2; Bound 4 ]) rows; cols ]
    | _ -> assert false
  in
  (* the regrouping we wrote by hand earlier is exactly split of canonical *)
  assert (Linear.compare split partitioned_rows = 0);
  (* dense in, dense out: split is a logical -> logical bijection *)
  assert (Layout.is_bijection_onto (Layout.of_linear split) ~size:128);
  (* agreement with the compose-based spec: (hi, lo) relabels hi*4 + lo *)
  for hi = 0 to 1 do
    for lo = 0 to 3 do
      for c = 0 to 15 do
        assert (
          Linear.eval split Coord.(Tuple [ Tuple [ Idx hi; Idx lo ]; Idx c ])
          = Linear.eval can Coord.(Tuple [ Idx ((hi * 4) + lo); Idx c ]))
      done
    done
  done

(* ---- divide: the partition, ((tile),(rest)), every tile kept ---- *)

let () =
  (* chop (8,16) row-major into 4x4 tiles *)
  let tiled = Linear.divide ~by:(Product [ Bound 4; Bound 4 ]) row_major in
  assert (
    Linear.compare
      tiled
      (Group
         [ Group [ Axis { size = 4; stride = 16 }; Axis { size = 4; stride = 1 } ]
         ; Group [ Axis { size = 2; stride = 64 }; Axis { size = 4; stride = 4 } ]
         ])
    = 0);
  (* a bijective relabeling: dense, and pointwise the same elements *)
  assert (Layout.is_bijection_onto (Layout.of_linear tiled) ~size:128);
  for tr = 0 to 3 do
    for tc = 0 to 3 do
      for br = 0 to 1 do
        for bc = 0 to 3 do
          assert (
            Linear.eval tiled Coord.(Tuple [ Tuple [ Idx tr; Idx tc ]; Tuple [ Idx br; Idx bc ] ])
            = Linear.eval row_major Coord.(Tuple [ Idx ((4 * br) + tr); Idx ((4 * bc) + tc) ]))
        done
      done
    done
  done;
  (* picking one tile is restriction on the rest coords, afterwards:
     tile (1,2) sits at base 64 + 8 = 72 *)
  let warp_tile =
    Restricted.restrict
      ~at:Coord.(Parts [ Free; Parts [ At 1; At 2 ] ])
      (Layout.storage tiled)
  in
  for tr = 0 to 3 do
    for tc = 0 to 3 do
      assert (
        Restricted.offset
          warp_tile
          Coord.(Tuple [ Tuple [ Idx tr; Idx tc ]; Tuple [ Idx 0; Idx 0 ] ])
        = 72 + (16 * tr) + tc)
    done
  done;
  (* a tiler that does not divide is refused *)
  (match Linear.divide ~by:(Product [ Bound 3; Bound 4 ]) row_major with
   | _ -> assert false
   | exception _ -> ())

(* ---- repeat: dense in => dense out, because cosize = size ---- *)

let () =
  let can = Linear.canonical logical_8x16 in
  assert (Linear.cosize can = 128);
  let three = Linear.repeat ~by:(Axis { size = 3; stride = 1 }) can in
  assert (Shape.size (Linear.shape three) = 384);
  assert (Layout.is_bijection_onto (Layout.of_linear three) ~size:384);
  (* padded physical layout: cosize > size, so repeat keeps the holes —
     injective (no aliasing) but not dense. Legal only with a physical
     codomain, which nothing ever composes past. *)
  let padded : Linear.t =
    Group [ Axis { size = 8; stride = 17 }; Axis { size = 16; stride = 1 } ]
  in
  assert (Linear.cosize padded = 135);
  let two = Layout.of_linear (Linear.repeat ~by:(Axis { size = 2; stride = 1 }) padded) in
  assert (Layout.is_injective two);
  assert (not (Layout.is_bijection_onto two ~size:270))

(* ---- selection is NOT a logical op: dropping elements loses density ---- *)

let () =
  (* only the even rows: injective but not dense, so it is not a legal
     logical layout, and compose rejects it. Selection belongs after the
     final compose into physical space. *)
  let evens : (Space.logical, Space.logical) Layout.t =
    Layout.of_linear (Group [ Axis { size = 4; stride = 32 }; Axis { size = 16; stride = 1 } ])
  in
  assert (Layout.is_injective evens);
  assert (not (Layout.is_bijection_onto evens ~size:128));
  (match Layout.compose evens (Layout.of_linear col_major) with
   | _ -> assert false
   | exception _ -> ())

(* ---- repeat by an arbitrary arrangement ---- *)

let () =
  (* 4x2 row-major grid of 8x16 tiles: tile (i,j) at (2i + j) * 128 *)
  let grid =
    Linear.repeat
      ~by:(Group [ Axis { size = 4; stride = 2 }; Axis { size = 2; stride = 1 } ])
      row_major
  in
  assert (Shape.size (Linear.shape grid) = 1024);
  assert (Layout.is_bijection_onto (Layout.of_linear grid) ~size:1024);
  assert (
    Linear.eval grid Coord.(Tuple [ Tuple [ Idx 1; Idx 1 ]; Tuple [ Idx 2; Idx 5 ] ])
    = (3 * 128) + 37)

(* ---- broadcast: copies at the SAME address ---- *)

let () =
  (* per-row scale read: logical space (copies=4, scales=8); storage
     aliases all copies to the one scale vector *)
  let scales : (Space.logical, Space.physical) Layout.t =
    Layout.broadcast ~by:(Bound 4) (Layout.storage (Axis { size = 8; stride = 1 }))
  in
  (* declared aliasing: non-injective, hence read-only *)
  assert (not (Layout.is_injective scales));
  (* the TV layout is a PLAIN dense bijection: thread (r, cg) owns its
     own logical copy (cg, r) — ownership never aliases *)
  let tv : (Space.thread_value, Space.logical) Layout.t =
    Layout.of_linear (Group [ Axis { size = 8; stride = 1 }; Axis { size = 4; stride = 8 } ])
  in
  let addr = Layout.compose tv scales in
  (* all four threads of a row group compute the same address: the
     hardware broadcast case *)
  for r = 0 to 7 do
    for cg = 0 to 3 do
      assert (Layout.offset addr Coord.(Tuple [ Idx r; Idx cg ]) = r)
    done
  done

let () =
  (* Broadcast on the LEFT of compose is rejected by the density gate:
     a replicated map is not a bijection *)
  let f : (Space.logical, Space.logical) Layout.t =
    Layout.of_linear (Group [ Broadcast { size = 2 }; Axis { size = 4; stride = 1 } ])
  in
  (match Layout.compose f (Layout.of_linear (Axis { size = 8; stride = 1 })) with
   | _ -> assert false
   | exception _ -> ())

(* ---- restricted layouts: the layout untouched, the restriction as data ---- *)

(* Same TV map as tv_linear, grouped with the executor (colgroup) axis
   outermost, as the compiler builds it for slicing. *)
let tv_by_warp : Linear.t =
  Group
    [ Axis { size = 4; stride = 4 }
    ; Group [ Axis { size = 8; stride = 16 }; Axis { size = 4; stride = 1 } ]
    ]

let () =
  let addr = Layout.compose (Layout.of_linear tv_by_warp) (Layout.storage col_major) in
  (* colgroup 2's slice: a Restricted.t — NOT a layout *)
  let sliced = Restricted.restrict ~at:Coord.(Parts [ At 2; Free ]) addr in
  (* the underlying layout is byte-identical to the unrestricted one *)
  assert (Restricted.layout sliced == addr);
  (* fixed slots shrink to Bound 1 in the restricted domain *)
  assert (
    Shape.compare
      (Restricted.shape sliced)
      (Product [ Bound 1; Product [ Bound 8; Bound 4 ] ])
    = 0);
  (* evaluation completes the coordinate (fixed slot takes Idx 0) and
     evaluates the original map *)
  for r = 0 to 7 do
    for v = 0 to 3 do
      assert (
        Restricted.offset sliced Coord.(Tuple [ Idx 0; Tuple [ Idx r; Idx v ] ])
        = Layout.offset addr Coord.(Tuple [ Idx 2; Tuple [ Idx r; Idx v ] ]))
    done
  done;
  (* an interior fix works the same way, no reordering *)
  let mid = Restricted.restrict ~at:Coord.(Parts [ Free; Parts [ At 5; Free ] ]) addr in
  for cg = 0 to 3 do
    for v = 0 to 3 do
      assert (
        Restricted.offset mid Coord.(Tuple [ Idx cg; Tuple [ Idx 0; Idx v ] ])
        = Layout.offset addr Coord.(Tuple [ Idx cg; Tuple [ Idx 5; Idx v ] ]))
    done
  done;
  (* out-of-bounds index is rejected at construction *)
  (match Restricted.restrict ~at:Coord.(Parts [ At 4; Free ]) addr with
   | _ -> assert false
   | exception _ -> ())

let () =
  (* a THREAD slice is just restriction: fix the thread's slots (cg and
     r together, leading and interior in one partial), leave values
     free. Thread (2,5)'s addresses: 2*32 + 5 + 8v. *)
  let addr = Layout.compose (Layout.of_linear tv_by_warp) (Layout.storage col_major) in
  let thread = Restricted.restrict ~at:Coord.(Parts [ At 2; Parts [ At 5; Free ] ]) addr in
  for v = 0 to 3 do
    assert (
      Restricted.offset thread Coord.(Tuple [ Idx 0; Tuple [ Idx 0; Idx v ] ]) = 69 + (8 * v))
  done;
  (* the same slice built hierarchically: warp slice, THEN thread slice —
     further restriction is the union of the restrictions *)
  let warp = Restricted.restrict ~at:Coord.(Parts [ At 2; Free ]) addr in
  let thread' = Restricted.restrict_more ~at:Coord.(Parts [ Free; Parts [ At 5; Free ] ]) warp in
  assert (Coord.compare_partial (Restricted.restriction thread') (Restricted.restriction thread) = 0);
  for v = 0 to 3 do
    assert (
      Restricted.offset thread' Coord.(Tuple [ Idx 0; Tuple [ Idx 0; Idx v ] ]) = 69 + (8 * v))
  done;
  (* re-fixing an already-fixed slot at a nonzero index is rejected *)
  (match Restricted.restrict_more ~at:Coord.(Parts [ At 1; Free ]) warp with
   | _ -> assert false
   | exception _ -> ())

let () =
  (* a swizzled layout needs no special case: nothing is ever split, the
     original map is evaluated at the completed coordinate *)
  let addr =
    Layout.compose
      (Layout.of_linear tv_by_warp)
      (Layout.with_swizzle (Layout.storage col_major) bank_swizzle)
  in
  let sliced = Restricted.restrict ~at:Coord.(Parts [ At 2; Free ]) addr in
  (* sw(64 + 5) = 65 — the naive "64 + sw(5)" would be 69 *)
  assert (Restricted.offset sliced Coord.(Tuple [ Idx 0; Tuple [ Idx 5; Idx 0 ] ]) = 65);
  for r = 0 to 7 do
    for v = 0 to 3 do
      assert (
        Restricted.offset sliced Coord.(Tuple [ Idx 0; Tuple [ Idx r; Idx v ] ])
        = Layout.offset addr Coord.(Tuple [ Idx 2; Tuple [ Idx r; Idx v ] ]))
    done
  done

let () =
  (* stage slicing: compose the stage-extended TV with the full storage,
     then restrict the composite. Thread (1,2) value 3 of stage 2:
     2*128 + 16 + 8 + 3 = 283. *)
  let storage_full = Linear.canonical (Product [ Bound 3; Product [ Bound 8; Bound 16 ] ]) in
  let addr =
    Layout.compose
      (Layout.of_linear (Group [ Axis { size = 3; stride = 128 }; tv_linear ]))
      (Layout.storage storage_full)
  in
  let stage2 = Restricted.restrict ~at:Coord.(Parts [ At 2; Free ]) addr in
  assert (
    Restricted.offset stage2 Coord.(Tuple [ Idx 0; Tuple [ Tuple [ Idx 1; Idx 2 ]; Idx 3 ] ])
    = 283)

let () =
  (* pinning a middle slot of a composite: identity relabel onto storage
     (4,(8,4)), then r = 5 fixed. Address = cg*32 + 5*4 + v. *)
  let can = Linear.canonical (Product [ Bound 4; Product [ Bound 8; Bound 4 ] ]) in
  let comp = Layout.compose (Layout.of_linear can) (Layout.storage can) in
  let a = Restricted.restrict ~at:Coord.(Parts [ Free; Parts [ At 5; Free ] ]) comp in
  for cg = 0 to 3 do
    for v = 0 to 3 do
      assert (
        Restricted.offset a Coord.(Tuple [ Idx cg; Tuple [ Idx 0; Idx v ] ])
        = (cg * 32) + 20 + v)
    done
  done

let () =
  (* hierarchical slicing on a composite: stage 2, then row 3 (union of
     restrictions). Address = 2*128 + 3*16 + col. *)
  let can = Linear.canonical (Product [ Bound 3; Product [ Bound 8; Bound 16 ] ]) in
  let comp = Layout.compose (Layout.of_linear can) (Layout.storage can) in
  let c =
    Restricted.restrict_more
      ~at:Coord.(Parts [ Free; Parts [ At 3; Free ] ])
      (Restricted.restrict ~at:Coord.(Parts [ At 2; Free ]) comp)
  in
  assert (
    Coord.compare_partial
      (Restricted.restriction c)
      Coord.(Parts [ At 2; Parts [ At 3; Free ] ])
    = 0);
  for col = 0 to 15 do
    assert (
      Restricted.offset c Coord.(Tuple [ Idx 0; Tuple [ Idx 0; Idx col ] ]) = 304 + col)
  done

let () =
  (* ownership queries need no restriction: which logical elements does
     thread (2,5) own, and where do they land under a reindexing, are
     plain evaluations of unrestricted maps. Addresses for that thread
     are a restriction of the PHYSICAL composite (the thread-slice test
     above). *)
  let owned = Layout.compose (Layout.of_linear tv_by_warp) (Layout.storage col_major) in
  for v = 0 to 3 do
    assert (
      Linear.eval tv_by_warp Coord.(Tuple [ Idx 2; Tuple [ Idx 5; Idx v ] ]) = 88 + v);
    assert (
      Layout.offset owned Coord.(Tuple [ Idx 2; Tuple [ Idx 5; Idx v ] ]) = 69 + (8 * v))
  done

let () =
  (* slicing a composite by an original flat index: the composite of the
     flat 384 view refines into (3,8,16), and the CALLER decomposes the
     index (unflatten is public): 100 = 0*128 + 6*16 + 4. *)
  let storage_full = Linear.canonical (Product [ Bound 3; Product [ Bound 8; Bound 16 ] ]) in
  let comp =
    Layout.compose
      (Layout.of_linear (Axis { size = 384; stride = 1 }))
      (Layout.storage storage_full)
  in
  (* the composite's domain is f's domain, the flat 384: pin index 100
     directly; canonical storage sends it to address 100 *)
  let c = Restricted.restrict ~at:(At 100) comp in
  assert (Restricted.offset c (Idx 0) = 100)

let () =
  (* restricting a Broadcast slot: just another completed coordinate *)
  let scales =
    Layout.broadcast ~by:(Bound 4) (Layout.storage (Axis { size = 8; stride = 1 }))
  in
  let one_copy = Restricted.restrict ~at:Coord.(Parts [ At 3; Free ]) scales in
  for r = 0 to 7 do
    assert (Restricted.offset one_copy Coord.(Tuple [ Idx 0; Idx r ]) = r)
  done

let () =
  let swizzled =
    Layout.with_swizzle
      (Layout.storage (Group [ Axis { size = 2; stride = 2 }; Axis { size = 2; stride = 1 } ]))
      { bits = 1; src = 2; dst = 0 }
  in
  (* a swizzle whose fields cross the footprint cannot be repeated:
     footprint 4, source field at bits [2,3) — copies would bleed into
     each other's swizzle *)
  (match Layout.repeat ~by:(Axis { size = 2; stride = 1 }) swizzled with
   | _ -> assert false
   | exception _ -> ());
  (* interleaving swizzled layouts has no defined meaning *)
  (match Layout.interleave ~by:(Axis { size = 2; stride = 1 }) swizzled with
   | _ -> assert false
   | exception _ -> ())

let () =
  (* arrangements are dense by definition, for repeat and interleave
     alike: a gapped [by] is a unit confusion, not padding — padding
     lives in the tile's own strides *)
  (match Linear.interleave ~by:(Axis { size = 2; stride = 2 }) row_major with
   | _ -> assert false
   | exception _ -> ());
  (match Linear.repeat ~by:(Axis { size = 2; stride = 2 }) row_major with
   | _ -> assert false
   | exception _ -> ());
  (* inter-stage padding, said honestly: repeat a tile whose own strides
     carry the pad — the padded rows tile has cosize 135, so stages are
     spaced 135 apart *)
  let padded : Linear.t =
    Group [ Axis { size = 8; stride = 17 }; Axis { size = 16; stride = 1 } ]
  in
  let staged = Linear.repeat ~by:(Axis { size = 2; stride = 1 }) padded in
  assert (
    Linear.eval staged Coord.(Tuple [ Idx 1; Tuple [ Idx 0; Idx 0 ] ]) = 135);
  (* a dense but permuted [by] is fine: copies in swapped cell slots *)
  let permuted =
    Linear.interleave
      ~by:(Group [ Axis { size = 2; stride = 1 }; Axis { size = 2; stride = 2 } ])
      (Axis { size = 4; stride = 1 })
  in
  assert (Layout.is_bijection_onto (Layout.of_linear permuted) ~size:16)

let () =
  (* malformed axis: strides are >= 1 *)
  (match Layout.of_linear (Axis { size = 4; stride = 0 }) with
   | _ -> assert false
   | exception _ -> ())

let () =
  (* thread 2's owned values, under physical-only restriction:
     TV: thread t value v -> logical (t, v), storage g column-major.
     Ownership is a plain evaluation of the unrestricted TV; thread 2's
     ADDRESSES are a restriction of the physical composite. Restricting
     the TV itself (logical codomain) is now a type error:

       let _ = Restricted.restrict ~at:Coord.(Parts [ At 2; Free ]) tv
  *)
  let tv : (Space.thread_value, Space.logical) Layout.t =
    Layout.of_linear (Group [ Axis { size = 8; stride = 4 }; Axis { size = 4; stride = 1 } ])
  in
  let g : (Space.logical, Space.physical) Layout.t =
    Layout.storage (Group [ Axis { size = 8; stride = 1 }; Axis { size = 4; stride = 8 } ])
  in
  let thread2 =
    Restricted.restrict ~at:Coord.(Parts [ At 2; Free ]) (Layout.compose tv g)
  in
  assert (Shape.compare (Restricted.shape thread2) (Product [ Bound 1; Bound 4 ]) = 0);
  for v = 0 to 3 do
    (* ownership: logical index 8 + v; address: g(row 2, v) = 2 + 8v *)
    assert (Layout.offset tv Coord.(Tuple [ Idx 2; Idx v ]) = 8 + v);
    assert (Restricted.offset thread2 Coord.(Tuple [ Idx 0; Idx v ]) = 2 + (8 * v))
  done

(* ---- random power-of-two dense pairs: every composite agrees with the
   semantic oracle ---- *)

let () =
  Random.init 42;
  let rec random_sizes k =
    if k = 0
    then []
    else (
      let p = 1 + Random.int (min 3 k) in
      (1 lsl p) :: random_sizes (k - p))
  in
  let shuffle l =
    List.map (fun x -> Random.bits (), x) l |> List.sort compare |> List.map snd
  in
  (* a random dense pow2 bijection: stride-sorted strides are running
     products of the sizes; the tree order is then shuffled *)
  let random_dense k =
    let sizes = shuffle (random_sizes k) in
    let leaves, _ =
      List.fold_left (fun (acc, s) n -> (n, s) :: acc, s * n) ([], 1) sizes
    in
    match shuffle leaves with
    | [] -> Linear.Axis { size = 1; stride = 1 }
    | ls -> Linear.Group (List.map (fun (size, stride) -> Linear.Axis { size; stride }) ls)
  in
  (* a random pow2-sized layout with arbitrary pow2 strides (holes fine) *)
  let random_strided k =
    match random_sizes k with
    | [] -> Linear.Axis { size = 1; stride = 1 }
    | ls ->
      Linear.Group
        (List.map (fun size -> Linear.Axis { size; stride = 1 lsl Random.int 8 }) ls)
  in
  (* enumeration oracle for density, to check the symbolic verdict *)
  let enum_dense l ~size =
    let s = Linear.shape l in
    Shape.size s = size
    &&
    let image =
      List.map (fun c -> Linear.eval l c) (Coord.enumerate s) |> List.sort compare
    in
    image = List.init size (fun i -> i)
  in
  for _ = 1 to 200 do
    let k = Random.int 8 in
    let f = random_dense k
    and g = random_strided k in
    (* the symbolic density check agrees with the enumeration oracle *)
    assert (Linear.is_dense f ~size:(1 lsl k) = enum_dense f ~size:(1 lsl k));
    assert (Linear.is_dense g ~size:(1 lsl k) = enum_dense g ~size:(1 lsl k));
    ignore g
  done

let () =
  (* swizzle cancellation: g's pre-swizzle addresses along f are
     0,3,4,7,8,11 (not strided) but its swizzle maps them to
     0,2,4,6,8,10 — the composite IS strided, 6a + 2b, only through the
     xor. The emitter's simplifier never rewrites a nonconstant xor, so
     this strided form is not recovered (Test_util counts it as
     affine-through-xor); the composite itself is an ordinary pair. *)
  let f : Linear.t = Group [ Axis { size = 2; stride = 3 }; Axis { size = 3; stride = 1 } ] in
  let g =
    Layout.with_swizzle
      (Layout.storage (Group [ Axis { size = 3; stride = 4 }; Axis { size = 2; stride = 3 } ]))
      { bits = 1; src = 1; dst = 0 }
  in
  (* the true composite, by the semantic definition, is 6a + 2b *)
  let shape_g = Layout.shape g in
  for a = 0 to 1 do
    for b = 0 to 2 do
      let x = Linear.eval f Coord.(Tuple [ Idx a; Idx b ]) in
      assert (Layout.offset g (Coord.unflatten shape_g x) = (6 * a) + (2 * b))
    done
  done;
  (* and composition simply produces it *)
  let comp = Layout.compose (Layout.of_linear f) g in
  for a = 0 to 1 do
    for b = 0 to 2 do
      assert (Layout.offset comp Coord.(Tuple [ Idx a; Idx b ]) = (6 * a) + (2 * b))
    done
  done;
  (* fixed-swizzle completeness relies on swizzle injectivity, so
     overlapping fields are excluded by construction: with the
     low-bit-clearing map x ^ (x & 1) — non-injective — the same
     layouts would admit the strided 6a + 2b under the SAME swizzle
     despite rejection *)
  (match
     Layout.with_swizzle
       (Layout.storage (Group [ Axis { size = 3; stride = 4 }; Axis { size = 2; stride = 3 } ]))
       { bits = 1; src = 0; dst = 0 }
   with
   | _ -> assert false
   | exception _ -> ())

(* ---- alias-freedom vs injectivity ---- *)

let () =
  (* declared replication: alias-free (valid physical) but not injective
     (hence not a legal store target) *)
  let scales =
    Layout.broadcast ~by:(Bound 4) (Layout.storage (Axis { size = 8; stride = 1 }))
  in
  assert (Layout.is_alias_free scales);
  assert (not (Layout.is_injective scales));
  (* genuine aliasing: two axes on the same stride — neither *)
  let bad = Layout.of_linear (Group [ Axis { size = 2; stride = 1 }; Axis { size = 2; stride = 1 } ]) in
  assert (not (Layout.is_alias_free bad));
  assert (not (Layout.is_injective bad));
  (* plain padded storage: both *)
  let padded = Layout.of_linear (Group [ Axis { size = 8; stride = 17 }; Axis { size = 16; stride = 1 } ]) in
  assert (Layout.is_alias_free padded);
  assert (Layout.is_injective padded)

let () =
  (* declared replication is INHERITED by composites: the composite's
     domain has no Broadcast slot, yet its aliases come from the storage.
     f = canonical(6), g = [Bcast 2; Axis 3:1]: composite x |-> x mod 3 *)
  let g = Layout.broadcast ~by:(Bound 2) (Layout.storage (Axis { size = 3; stride = 1 })) in
  let comp = Layout.compose (Layout.of_linear (Axis { size = 6; stride = 1 })) g in
  for x = 0 to 5 do
    assert (Layout.offset comp (Idx x) = x mod 3)
  done;
  assert (Layout.is_alias_free comp);
  assert (not (Layout.is_injective comp));
  (* whereas genuine aliasing in the storage stays aliasing in the composite *)
  let bad = Layout.of_linear (Group [ Axis { size = 2; stride = 1 }; Axis { size = 2; stride = 1 } ]) in
  let comp_bad = Layout.compose (Layout.of_linear (Axis { size = 4; stride = 1 })) bad in
  assert (not (Layout.is_alias_free comp_bad))

(* ---- inverse of a dense layout: the ownership map ---- *)

let () =
  (* the law: inverse undoes the layout, landing on the canonical index *)
  let law (l : Linear.t) =
    let inv = Linear.inverse l in
    let s = Linear.shape l in
    let can = Linear.canonical s in
    List.iter
      (fun c ->
        assert (Linear.eval inv (Coord.unflatten (Linear.shape inv) (Linear.eval l c))
                = Linear.eval can c))
      (Coord.enumerate s)
  in
  List.iter law [ col_major; row_major; partitioned_rows; tv_linear; tv_by_warp ];
  (* the inverse of a canonical layout is itself *)
  assert (Linear.compare (Linear.inverse (Linear.canonical logical_8x16)) row_major = 0);
  (* ownership: which (thread, value) holds tile element 27 = (1, 11)?
     tv_by_warp sends (cg=2,(r=1,v=3)) there; that coordinate's canonical
     index in (4,(8,4)) is 2*32 + 1*4 + 3 = 71 *)
  let inv = Linear.inverse tv_by_warp in
  assert (Linear.eval inv (Coord.unflatten (Linear.shape inv) 27) = 71);
  (* typed: the inverse of a (tv, logical) map is a (logical, tv) map, and
     composing the two is the identity relabel *)
  let tv : (Space.thread_value, Space.logical) Layout.t = Layout.of_linear tv_by_warp in
  let ident = Layout.compose tv (Layout.inverse tv) in
  let can = Linear.canonical (Layout.shape tv) in
  List.iter
    (fun c -> assert (Layout.offset ident c = Linear.eval can c))
    (Coord.enumerate (Layout.shape tv));
  (* THE use of the ownership map: RETILING. Two thread-value maps over
     the same tile are related by copy-coordinate -> element ->
     MMA-coordinate, a composition with the inverse. It is a map between
     coordinate spaces and nothing more (what it costs to realize on data
     is not a layout question). Here: copy = tv_linear ((r,cg),v), mma =
     tv_by_warp (cg,(r,v)), same thread identity (r,cg): ((r,cg),v) goes
     to (cg,(r,v)), canonical index 32cg + 4r + v. *)
  let copy_tv : (Space.thread_value, Space.logical) Layout.t = Layout.of_linear tv_linear in
  let mma_tv : (Space.thread_value, Space.logical) Layout.t = Layout.of_linear tv_by_warp in
  let retile = Layout.compose copy_tv (Layout.inverse mma_tv) in
  for r = 0 to 7 do
    for cg = 0 to 3 do
      for v = 0 to 3 do
        assert (
          Layout.offset retile Coord.(Tuple [ Tuple [ Idx r; Idx cg ]; Idx v ])
          = (32 * cg) + (4 * r) + v)
      done
    done
  done;
  (* the contrasting case: both dense, yet the correspondence does NOT
     fix the lane coordinate. 32 lanes x 2 values: copy = 2*lane + v,
     target = lane + 32*v. copy (0,1) holds element 1, which the target
     puts at (1,0); 62 of the 64 coordinates map to a different lane. *)
  let copy : (Space.thread_value, Space.logical) Layout.t =
    Layout.of_linear (Group [ Axis { size = 32; stride = 2 }; Axis { size = 2; stride = 1 } ])
  in
  let target : (Space.thread_value, Space.logical) Layout.t =
    Layout.of_linear (Group [ Axis { size = 32; stride = 1 }; Axis { size = 2; stride = 32 } ])
  in
  let corr = Layout.compose copy (Layout.inverse target) in
  let target_shape = Layout.shape target in
  assert (
    Coord.unflatten target_shape (Layout.offset corr Coord.(Tuple [ Idx 0; Idx 1 ]))
    = Coord.(Tuple [ Idx 1; Idx 0 ]));
  let lane_changes = ref 0 in
  for lane = 0 to 31 do
    for v = 0 to 1 do
      match Coord.unflatten target_shape (Layout.offset corr Coord.(Tuple [ Idx lane; Idx v ])) with
      | Coord.Tuple [ Coord.Idx lane'; _ ] -> if lane' <> lane then incr lane_changes
      | _ -> assert false
    done
  done;
  assert (!lane_changes = 62);
  (* only dense layouts invert *)
  (match Linear.inverse (Group [ Axis { size = 8; stride = 17 }; Axis { size = 16; stride = 1 } ]) with
   | _ -> assert false
   | exception _ -> ())

(* ---- Decide: the strided form, and its absence ---- *)

let () =
  let open Expr in
  (* uniqueness: the coefficients of an affine form are forced, so the
     decided form is the one the values dictate *)
  let l : (Space.logical, Space.physical) Layout.t =
    Layout.storage (Group [ Axis { size = 4; stride = 8 }; Axis { size = 8; stride = 1 } ])
  in
  (match Layout.strided_form l with
   | Some e -> assert (to_string e = "8*c0 + c1")
   | None -> assert false);
  (* a reshape of one axis: no affine form over the coordinates, but a
     strided form over a refinement of that axis *)
  let f : (Space.logical, Space.logical) Layout.t =
    Layout.of_linear (Axis { size = 16; stride = 1 })
  in
  let g : (Space.logical, Space.physical) Layout.t =
    Layout.storage (Group [ Axis { size = 4; stride = 40 }; Axis { size = 4; stride = 1 } ])
  in
  let reshaped = Layout.compose f g in
  assert (Layout.to_expr reshaped = "40*(c / 4) + (c % 4)");
  (* padding makes it non-affine in c, and the digits are the proof *)
  match Layout.strided_form reshaped with
  | Some e -> assert (not (Expr.is_affine e))
  | None -> assert false
;;

(* ---- to_expr: the generated per-lane math ---- *)

let () =
  (* The composite (4:4,(8:16,4:1)) . (8:1,16:8) has a single strided
     form, and it is decided, not searched for. *)
  let addr = Layout.compose (Layout.of_linear tv_by_warp) (Layout.storage col_major) in
  assert (Layout.to_expr addr = "32*c0 + c1_0 + 8*c1_1");
  (* the swizzled version is not affine; it emits as the pipeline *)
  let swizzled =
    Layout.compose
      (Layout.of_linear tv_by_warp)
      (Layout.with_swizzle (Layout.storage col_major) bank_swizzle)
  in
  assert (Option.is_none (Layout.strided_form swizzled));
  (* warp 2's slice: the pin became a constant and folded *)
  let sliced = Restricted.restrict ~at:Coord.(Parts [ At 2; Free ]) addr in
  assert (Restricted.to_expr sliced = "c1_0 + 8*c1_1 + 64");
  (* (2,3) -> (3,2): no strided form exists; the emitted expression
     keeps a residual modulus and division and is still exact *)
  let f : (Space.logical, Space.logical) Layout.t =
    Layout.of_linear (Group [ Axis { size = 2; stride = 3 }; Axis { size = 3; stride = 1 } ])
  in
  let g : (Space.logical, Space.physical) Layout.t =
    Layout.storage (Group [ Axis { size = 3; stride = 1 }; Axis { size = 2; stride = 3 } ])
  in
  let comp = Layout.compose f g in
  (* PROVABLY none: both axis sizes are prime, so the only refinement is
     the trivial one, and the size-3 axis lands at 0,3,1 *)
  assert (Option.is_none (Layout.strided_form comp));
  (* A strided form that exists only THROUGH the swizzle: 2c xor c on
     c in {0,1} has addresses 0,3 = 3c. Reading values settles it. *)
  let through_xor : (Space.logical, Space.physical) Layout.t =
    Layout.with_swizzle (Layout.storage (Axis { size = 2; stride = 2 })) { bits = 1; src = 1; dst = 0 }
  in
  assert (Layout.offset through_xor (Idx 0) = 0 && Layout.offset through_xor (Idx 1) = 3);
  assert (Expr.to_string (Layout.expr through_xor) = "let a0 = 2*c in a0 ^ ((a0 / 2) % 2)");
  assert (Layout.to_expr through_xor = "3*c");
  (* pow2 everywhere: composite through a swizzled buffer, the whole
     GMMA-style case, is one affine sum under one xor *)
  let tv : (Space.thread_value, Space.logical) Layout.t =
    Layout.of_linear (Group [ Axis { size = 32; stride = 8 }; Axis { size = 8; stride = 1 } ])
  in
  let buf =
    Layout.with_swizzle
      (Layout.storage (Group [ Axis { size = 4; stride = 64 }; Axis { size = 64; stride = 1 } ]))
      { bits = 2; src = 6; dst = 3 }
  in
  assert (Layout.to_expr (Layout.compose tv buf) = "let x1 = 8*c0 + c1 in x1 ^ (8*((x1 / 64) % 4))");
  (* the map with no strided form emits as the pipeline: the stage index
     bound once, its digits read off it *)
  assert (Layout.to_expr comp = "let x1 = 3*c0 + c1 in (x1 / 2) + 3*(x1 % 2)")

let () = Test_util.report "layouts"
let () = print_endline "all layout tests passed"
