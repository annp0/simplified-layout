(* CUTLASS/CuTe layout audit, tranche 1: express NVIDIA's published atom
   layouts in this algebra and enumeration-check them.

   CuTe prints TV layouts against a COLUMN-major linearization of the
   (M,N)/(M,K) tile; our logical convention is row-major, so each atom
   is transcribed by recomputing strides against the row-major canonical
   space — the ownership function is identical, only the encoding
   differs.

   Sources: CuTe 0t_mma_atom docs (SM70 quadpair, SM90 GMMA); PTX ISA
   mma fragment tables (SM80 m16n8k16).

   Remaining inventory (TODO):
   - MN-major GMMA swizzle atoms; tf32 / 8-bit atom variants
   - TMA tiling patterns
   - cp.async copy atoms *)

open Layouts
module Layout = Test_util.Checked_layout

let dense l ~size = Layout.is_bijection_onto (Layout.of_linear l) ~size

(* --- SM70_8x8x4 (Volta quadpair), NT ---
   CuTe: CLayout = (8,8):(1,8) over col-major (8,8), i.e. thread t,
   value v owns C(m,n) = (t, v). Row-major (8,8): offset = 8t + v. *)
let () =
  let c_frag : Linear.t =
    Group [ Axis { size = 8; stride = 8 }; Axis { size = 8; stride = 1 } ]
  in
  assert (dense c_frag ~size:64);
  (* thread 3, value 5 owns C(3,5) *)
  assert (Linear.eval c_frag Coord.(Tuple [ Idx 3; Idx 5 ]) = (3 * 8) + 5)

(* CuTe: ALayout = ((4,2),4):((8,4),1) over col-major (M=8,K=4), i.e.
   thread (t4,t2), value v owns A(m,k) = (4*t2 + v, t4).
   Row-major (8,4): offset = 4m + k = 16*t2 + 4*v + t4. *)
let () =
  let a_frag : Linear.t =
    Group
      [ Group [ Axis { size = 4; stride = 1 }; Axis { size = 2; stride = 16 } ]
      ; Axis { size = 4; stride = 4 }
      ]
  in
  assert (dense a_frag ~size:32);
  (* thread (1,1), value 2 owns A(6,1) -> 4*6 + 1 = 25 *)
  assert (Linear.eval a_frag Coord.(Tuple [ Tuple [ Idx 1; Idx 1 ]; Idx 2 ]) = 25)

(* --- SM80 mma.m16n8k16 C fragment (PTX ISA fragment table) ---
   lane = 4g + t4; values (vm, vn); owns C(m,n) = (g + 8*vm, 2*t4 + vn).
   Row-major (16,8): offset = 8g + 64*vm + 2*t4 + vn. *)
let sm80_c : Linear.t =
  Group
    [ Group [ Axis { size = 8; stride = 8 }; Axis { size = 4; stride = 2 } ]
    ; Group [ Axis { size = 2; stride = 64 }; Axis { size = 2; stride = 1 } ]
    ]

let () =
  assert (dense sm80_c ~size:128);
  let offset ~g ~t4 ~vm ~vn =
    Linear.eval sm80_c Coord.(Tuple [ Tuple [ Idx g; Idx t4 ]; Tuple [ Idx vm; Idx vn ] ])
  in
  (* PTX: lane 0 owns (0,0) (0,1) (8,0) (8,1) *)
  assert (offset ~g:0 ~t4:0 ~vm:0 ~vn:0 = 0);
  assert (offset ~g:0 ~t4:0 ~vm:0 ~vn:1 = 1);
  assert (offset ~g:0 ~t4:0 ~vm:1 ~vn:0 = 64);
  (* PTX: lane 5 = (g=1,t4=1) owns (1,2) (1,3) (9,2) (9,3) *)
  assert (offset ~g:1 ~t4:1 ~vm:0 ~vn:0 = 10);
  assert (offset ~g:1 ~t4:1 ~vm:1 ~vn:1 = 75)

(* --- SM90 GMMA operand replication ---
   CuTe: shape (128,(64,16)), stride (0,(1,64)) — all 128 warpgroup
   threads replicated over the whole (64,16) SMEM operand (GMMA reads
   via descriptor). In CuTe that is a stride-0 TV layout; here it is
   NOT: ownership stays a dense bijection over the copies-extended
   logical space (128,(64,16)), and the aliasing is broadcast STORAGE. *)
let () =
  let tile = Linear.canonical (Product [ Bound 64; Bound 16 ]) in
  let storage : (Space.logical, Space.physical) Layout.t =
    Layout.broadcast ~by:(Bound 128) (Layout.storage tile)
  in
  let tv : (Space.thread_value, Space.logical) Layout.t =
    Layout.of_linear
      (Linear.canonical (Product [ Bound 128; Product [ Bound 64; Bound 16 ] ]))
  in
  let addr = Layout.compose tv storage in
  let off ~t ~m ~k = Layout.offset addr Coord.(Tuple [ Idx t; Tuple [ Idx m; Idx k ] ]) in
  (* every thread computes the same address for the same element *)
  assert (off ~t:0 ~m:3 ~k:5 = off ~t:127 ~m:3 ~k:5);
  assert (off ~t:64 ~m:3 ~k:5 = (3 * 16) + 5);
  (* declared replication: alias-free, not injective *)
  assert (Layout.is_alias_free storage);
  assert (not (Layout.is_injective storage))

(* ================= tranche 2 ================= *)

(* --- SM80 mma.m16n8k16 A fragment (PTX ISA fragment table) ---
   A is (16,16) = (m,k). lane = 4g + t; values a0..a7 indexed by bits
   (v_k8, v_m, v_lo) high to low; thread (g,t) value (v_k8,v_m,v_lo)
   owns A(g + 8*v_m, 2t + 8*v_k8 + v_lo).
   Row-major (16,16): offset = 16m + k. *)
let sm80_a : Linear.t =
  Group
    [ Group [ Axis { size = 8; stride = 16 }; Axis { size = 4; stride = 2 } ]
    ; Group
        [ Axis { size = 2; stride = 8 }
        ; Axis { size = 2; stride = 128 }
        ; Axis { size = 2; stride = 1 }
        ]
    ]

let () =
  assert (dense sm80_a ~size:256);
  let offset ~g ~t ~vk8 ~vm ~vlo =
    Linear.eval
      sm80_a
      Coord.(Tuple [ Tuple [ Idx g; Idx t ]; Tuple [ Idx vk8; Idx vm; Idx vlo ] ])
  in
  (* lane 0, a0 owns A(0,0) *)
  assert (offset ~g:0 ~t:0 ~vk8:0 ~vm:0 ~vlo:0 = 0);
  (* lane 5 = (g=1,t=1), a6 = (1,1,0) owns A(9,10) -> 16*9 + 10 *)
  assert (offset ~g:1 ~t:1 ~vk8:1 ~vm:1 ~vlo:0 = 154);
  (* lane 3 = (g=0,t=3), a1 = (0,0,1) owns A(0,7) *)
  assert (offset ~g:0 ~t:3 ~vk8:0 ~vm:0 ~vlo:1 = 7)

(* --- SM80 mma.m16n8k16 B fragment (PTX ISA fragment table) ---
   B is (16,8) = (k,n). Thread (g,t) value (v_hi, v_lo) owns
   B(2t + 8*v_hi + v_lo, g). Row-major (16,8): offset = 8k + n. *)
let sm80_b : Linear.t =
  Group
    [ Group [ Axis { size = 8; stride = 1 }; Axis { size = 4; stride = 16 } ]
    ; Group [ Axis { size = 2; stride = 64 }; Axis { size = 2; stride = 8 } ]
    ]

let () =
  assert (dense sm80_b ~size:128);
  let offset ~g ~t ~vhi ~vlo =
    Linear.eval sm80_b Coord.(Tuple [ Tuple [ Idx g; Idx t ]; Tuple [ Idx vhi; Idx vlo ] ])
  in
  assert (offset ~g:0 ~t:0 ~vhi:0 ~vlo:0 = 0);
  (* lane 5 = (g=1,t=1), b3 owns B(11,1) -> 8*11 + 1 *)
  assert (offset ~g:1 ~t:1 ~vhi:1 ~vlo:1 = 89)

(* --- ldmatrix m8n8 fragment (PTX) ---
   Thread t = 4g + q holds elements (g, 2q) and (g, 2q + 1) of the 8x8
   matrix — the same quad pattern as the mma operand fragments, which
   is the entire reason ldmatrix exists. x2/x4 are repeats of this. *)
let ldmatrix_frag : Linear.t =
  Group
    [ Group [ Axis { size = 8; stride = 8 }; Axis { size = 4; stride = 2 } ]
    ; Axis { size = 2; stride = 1 }
    ]

let () =
  assert (dense ldmatrix_frag ~size:64);
  assert (Linear.eval ldmatrix_frag Coord.(Tuple [ Tuple [ Idx 5; Idx 3 ]; Idx 1 ]) = 47)

(* --- SM90 GMMA 64x128 accumulator (CuTe 0t_mma_atom docs) ---
   CuTe prints ((4,8,4),(2,2,16)) : ((128,1,16),(64,8,512)) over the
   COL-major linearization i = m + 64n. Every stride is pure-m or
   pure-n, so it transcribes axis-by-axis to row-major (64,128)
   (offset = 128m + n): threads (4,8,4):(2,128,2048), values
   (2,2,16):(1,1024,8). 128 threads x 64 values, dense on 8192. *)
let sm90_c : Linear.t =
  Group
    [ Group
        [ Axis { size = 4; stride = 2 }
        ; Axis { size = 8; stride = 128 }
        ; Axis { size = 4; stride = 2048 }
        ]
    ; Group
        [ Axis { size = 2; stride = 1 }
        ; Axis { size = 2; stride = 1024 }
        ; Axis { size = 16; stride = 8 }
        ]
    ]

let () =
  assert (dense sm90_c ~size:8192);
  (* CuTe col-major spot checks: thread (1,0,0) strides 128 col-major
     = element (m,n) = (0,2) = row-major 2; value (0,1,0) strides 8
     col-major = (8,0) = row-major 1024 *)
  let offset t v = Linear.eval sm90_c Coord.(Tuple [ t; v ]) in
  assert (offset Coord.(Tuple [ Idx 1; Idx 0; Idx 0 ]) Coord.(Tuple [ Idx 0; Idx 0; Idx 0 ]) = 2);
  assert (offset Coord.(Tuple [ Idx 0; Idx 0; Idx 0 ]) Coord.(Tuple [ Idx 0; Idx 1; Idx 0 ]) = 1024)

(* --- GMMA canonical K-major SMEM swizzle atoms (mma_traits_sm90_gmma.hpp) ---
   Source: Swizzle<B,4,3> on byte offsets over an (8 rows, 2^B * 16
   bytes) core. For half elements that is uniformly
   {bits = B; src = 6; dst = 3} over (8, 8 * 2^B) elements:
   dst [3, 3+B) = 16-byte-unit index, src [6, 6+B) = row bits.
     INTER: B=0 (no swizzle), core (8,8)
     SW32:  B=1, core (8,16)
     SW64:  B=2, core (8,32)
     SW128: B=3, core (8,64) *)
let gmma_atom ~b =
  let cols = 8 * (1 lsl b) in
  let base =
    Layout.storage (Group [ Axis { size = 8; stride = cols }; Axis { size = cols; stride = 1 } ])
  in
  if b = 0 then base else Layout.with_swizzle base { bits = b; src = 6; dst = 3 }

let () =
  List.iter
    (fun b ->
      let atom = gmma_atom ~b in
      let size = 8 * 8 * (1 lsl b) in
      (* each atom is a bijection on its core: swizzling never loses data *)
      assert (Layout.is_bijection_onto atom ~size))
    [ 0; 1; 2; 3 ];
  (* SW128, the classic: 16-byte unit u of row r lands at unit (u xor r),
     so a fixed unit column hits all 8 unit positions across the 8 rows —
     the bank-conflict-free property *)
  let sw128 = gmma_atom ~b:3 in
  for r = 0 to 7 do
    for u = 0 to 7 do
      let off = Layout.offset sw128 Coord.(Tuple [ Idx r; Idx (8 * u) ]) in
      assert (off / 8 mod 8 = u lxor r);
      assert (off / 64 = r)
    done
  done

(* --- the two arrangements of 2 copies of the tile (4):(1) ---
     [repeat]     (CuTe logical_product(tile, copies), blocked_product):
                  copies side by side — ((2),(4)) : ((4),(1))
     [interleave] (CuTe logical_product(copies, tile), operands exchanged):
                  copies dealt out    — ((2),(4)) : ((1),(2))
   CuTe's raked_product is the FIRST of these with its coordinate groups
   exchanged per mode, not the second; see test_usage_table. Both dense. *)
let () =
  let tile : Linear.t = Axis { size = 4; stride = 1 } in
  let copies : Linear.t = Axis { size = 2; stride = 1 } in
  let blocked = Linear.repeat ~by:copies tile in
  assert (
    Linear.compare blocked (Group [ Axis { size = 2; stride = 4 }; Axis { size = 4; stride = 1 } ])
    = 0);
  assert (dense blocked ~size:8);
  let raked = Linear.interleave ~by:copies tile in
  assert (
    Linear.compare raked (Group [ Axis { size = 2; stride = 1 }; Axis { size = 4; stride = 2 } ])
    = 0);
  assert (dense raked ~size:8);
  (* copy 1 of raked sits at the odd offsets *)
  assert (Linear.eval raked Coord.(Tuple [ Idx 1; Idx 3 ]) = 7)

(* --- multi-stage swizzled SMEM buffer: 3 stages of the SW128 atom ---
   The swizzle's fields end at bit 9 and the atom's footprint is 2^9
   elements, so stage offsets commute with the swizzle: each stage is
   independently swizzled. This is the Hopper pipeline buffer. *)
let () =
  let staged = Layout.repeat ~by:(Axis { size = 3; stride = 1 }) (gmma_atom ~b:3) in
  assert (Layout.is_bijection_onto staged ~size:1536);
  let atom = gmma_atom ~b:3 in
  for r = 0 to 7 do
    for e = 0 to 63 do
      assert (
        Layout.offset staged Coord.(Tuple [ Idx 1; Tuple [ Idx r; Idx e ] ])
        = 512 + Layout.offset atom Coord.(Tuple [ Idx r; Idx e ]))
    done
  done

(* --- DERIVATION entry: the warp-tile pipeline built from ops only ---
   The transcription entries above validate the representation; this
   validates the ALGEBRA (a missing op is invisible to transcription —
   that is how [divide]'s absence went unnoticed). A (32,16) CTA tile
   is divided into (16,8) mma tiles; mma tile (1,0) is picked by
   restriction; the CTA-wide TV map is the SM80 C fragment interleaved
   by the (2,2) warp grid (each warp's elements dealt into the rest
   digits); composition pins the warp coordinate by pullback. No
   hand-written composite anywhere. Element (m,n) of tile (1,0) sits at
   256 + 16m + n. *)
let () =
  let cta = Linear.canonical (Product [ Bound 32; Bound 16 ]) in
  let tiled = Layout.divide ~by:(Product [ Bound 16; Bound 8 ]) (Layout.storage cta) in
  let cta_tv =
    Linear.interleave
      ~by:(Group [ Axis { size = 2; stride = 2 }; Axis { size = 2; stride = 1 } ])
      sm80_c
  in
  (* compose the CTA-wide TV onto the tiled storage, then slice: the
     warp coordinate is a slot of the composite's domain *)
  let addr =
    Restricted.restrict
      ~at:Coord.(Parts [ Parts [ At 1; At 0 ]; Free ])
      (Layout.compose (Layout.of_linear cta_tv) tiled)
  in
  for g = 0 to 7 do
    for t4 = 0 to 3 do
      for vm = 0 to 1 do
        for vn = 0 to 1 do
          let m = g + (8 * vm)
          and n = (2 * t4) + vn in
          assert (
            Restricted.offset
              addr
              Coord.(
                Tuple
                  [ Tuple [ Idx 0; Idx 0 ]
                  ; Tuple [ Tuple [ Idx g; Idx t4 ]; Tuple [ Idx vm; Idx vn ] ]
                  ])
            = 256 + (16 * m) + n)
        done
      done
    done
  done
;;

(* --- DERIVATION: the SM90 64x128 accumulator from the SM80 fragment ---
   The warpgroup accumulator is not new hardware wiring: it is the SM80
   m16n8 C fragment tiled over (64,128) — divide into (16,8) mma tiles,
   deal the fragment across the (4,16) rest grid (warps down M,
   per-thread iteration across N), compose. Checked equal to the
   transcription pointwise over all 8192 coordinates, under the
   coordinate correspondence
     sm90 thread (t4,g,w), value (vn,vm,nn)
       <->  derived ((w,nn), ((g,t4),(vm,vn))). *)
let () =
  let tiled =
    Linear.divide
      ~by:(Product [ Bound 16; Bound 8 ])
      (Linear.canonical (Product [ Bound 64; Bound 128 ]))
  in
  let cta_tv =
    Linear.interleave ~by:(Linear.canonical (Product [ Bound 4; Bound 16 ])) sm80_c
  in
  let derived = Layout.compose (Layout.of_linear cta_tv) (Layout.of_linear tiled) in
  for t4 = 0 to 3 do
    for g = 0 to 7 do
      for w = 0 to 3 do
        for vn = 0 to 1 do
          for vm = 0 to 1 do
            for nn = 0 to 15 do
              assert (
                Layout.offset
                  derived
                  Coord.(
                    Tuple
                      [ Tuple [ Idx w; Idx nn ]
                      ; Tuple [ Tuple [ Idx g; Idx t4 ]; Tuple [ Idx vm; Idx vn ] ]
                      ])
                = Linear.eval
                    sm90_c
                    Coord.(
                      Tuple
                        [ Tuple [ Idx t4; Idx g; Idx w ]
                        ; Tuple [ Idx vn; Idx vm; Idx nn ]
                        ]))
            done
          done
        done
      done
    done
  done
;;

(* ============ the GEMM mainloop dataflow, derived end to end ============
   INPUTS (choices): A-tile (8,32) halves, gmem lda 40, 16B vectors,
   one warp copying, 2 smem stages, SW64 swizzle, partitioning
   arrangements as dense layouts.
   AXIOMS: the ldmatrix fragment (hardware wiring), the swizzle family.
   Everything else is ops: divide / interleave / repeat / compose /
   restrict. No hand-written composite anywhere. *)
let () =
  let tile = Linear.canonical (Product [ Bound 8; Bound 32 ]) in
  let gmem : (Space.logical, Space.physical) Layout.t =
    Layout.storage (Group [ Axis { size = 8; stride = 40 }; Axis { size = 32; stride = 1 } ])
  in
  (* two stages of the swizzled SW64 atom: the pipeline buffer *)
  let smem = Layout.repeat ~by:(Axis { size = 2; stride = 1 }) (gmma_atom ~b:2) in
  (* ---- writer: the gmem -> smem copy partition ---- *)
  (* chop the tile into 16-byte vectors; each of 32 lanes owns one
     vector, lanes fastest across the (row, veccol) grid = coalesced.
     Lane l = 4r + v owns vector (r, v). *)
  let tiled_v = Linear.divide ~by:(Product [ Bound 1; Bound 8 ]) tile in
  let writer_tv =
    Linear.interleave ~by:(Axis { size = 32; stride = 1 }) (Axis { size = 8; stride = 1 })
  in
  let writer_logical = Layout.compose (Layout.of_linear writer_tv) (Layout.of_linear tiled_v) in
  (* coalescing, asserted in gmem: vectors are contiguous, and within a
     quad consecutive lanes read consecutive 16B vectors *)
  let writer_gmem = Layout.compose writer_logical gmem in
  for l = 0 to 31 do
    let a0 = Layout.offset writer_gmem Coord.(Tuple [ Idx l; Idx 0 ]) in
    for e = 1 to 7 do
      assert (Layout.offset writer_gmem Coord.(Tuple [ Idx l; Idx e ]) = a0 + e)
    done;
    if l mod 4 < 3
    then assert (Layout.offset writer_gmem Coord.(Tuple [ Idx (l + 1); Idx 0 ]) = a0 + 8)
  done;
  (* ---- both sides, staged: the stage axis is added at the leaves ---- *)
  let stage = Linear.Axis { size = 2; stride = 256 } in
  let staged_tiled_v = Layout.of_linear (Group [ stage; tiled_v ]) in
  let writer_staged =
    Layout.compose (Layout.of_linear (Group [ stage; writer_tv ])) staged_tiled_v
  in
  let writer_smem = Layout.compose writer_staged smem in
  (* vectorization survives the swizzle: every lane's smem vector is
     16B-aligned and contiguous *)
  for s = 0 to 1 do
    for l = 0 to 31 do
      let a0 = Layout.offset writer_smem Coord.(Tuple [ Idx s; Tuple [ Idx l; Idx 0 ] ]) in
      assert (a0 mod 8 = 0);
      for e = 1 to 7 do
        assert (
          Layout.offset writer_smem Coord.(Tuple [ Idx s; Tuple [ Idx l; Idx e ] ]) = a0 + e)
      done
    done
  done;
  (* ---- reader: smem -> register fragments ---- *)
  (* the tile is four 8x8 ldmatrix matrices; the fragment axiom is dealt
     across them (matrices become per-thread values) *)
  let tiled8 = Linear.divide ~by:(Product [ Bound 8; Bound 8 ]) tile in
  let reader_tv = Linear.interleave ~by:(Axis { size = 4; stride = 1 }) ldmatrix_frag in
  let staged_tiled8 = Layout.of_linear (Group [ stage; tiled8 ]) in
  let reader_staged =
    Layout.compose (Layout.of_linear (Group [ stage; reader_tv ])) staged_tiled8
  in
  let reader_smem = Layout.compose reader_staged smem in
  (* both pipelines cover the staged space exactly: every element owned
     once by the copy and once by the mma fetch *)
  assert (Layout.is_bijection_onto writer_staged ~size:512);
  assert (Layout.is_bijection_onto reader_staged ~size:512);
  (* ---- integration: same logical element => same smem byte ---- *)
  let addr_of = Array.make 512 (-1) in
  List.iter
    (fun c -> addr_of.(Layout.offset writer_staged c) <- Layout.offset writer_smem c)
    (Coord.enumerate (Layout.shape writer_smem));
  List.iter
    (fun c -> assert (Layout.offset reader_smem c = addr_of.(Layout.offset reader_staged c)))
    (Coord.enumerate (Layout.shape reader_smem));
  (* ---- stage slice, as the pipeline would take it ---- *)
  let stage1 = Restricted.restrict ~at:Coord.(Parts [ At 1; Free ]) reader_smem in
  List.iter
    (fun c ->
      match c with
      | Coord.Tuple [ Coord.Idx 0; rest ] ->
        assert (
          Restricted.offset stage1 Coord.(Tuple [ Idx 0; rest ])
          = Layout.offset reader_smem Coord.(Tuple [ Idx 1; rest ]))
      | _ -> ())
    (Coord.enumerate (Restricted.shape stage1))
;;

let () = print_endline "cutlass atom audit passed (incl. GEMM mainloop derivation)"
let () = Test_util.report "cutlass atoms"
