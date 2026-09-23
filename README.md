# layouts

A layout algebra for GPU tensor kernels, in OCaml, and the paper describing it
(`paper/layout-algebra.tex`).

A layout maps the coordinates of a tile to integers. Every layout names the
space its input and output live in: a logical index, a thread-value index, or a
physical offset. What a layout must satisfy follows from that: into logical or
thread-value space it is a dense bijection; into physical space it is
alias-free, and injective if it is written through; nothing maps out of a
physical offset. Composition requires only that the right operand be a dense
bijection onto the left operand's coordinates. Whether a composite is itself a
layout, over a possibly finer shape, is decided afterwards (`Decide`), and the
emitted address arithmetic is that layout when it exists and the composite
otherwise.

## Layout of the repository

    lib/
      space.mli     the three index spaces
      shape, coord  shapes, coordinates, flattening
      linear        strides and replication: the layouts of the paper's Definition 1
      swizzle       the physical-to-physical XOR bijection
      layout        layouts with their spaces; composition; emission
      restricted    a layout with some coordinates fixed
      decide        is this map a layout? the decision procedure of the paper's Section 4
      expr          the emitted integer expressions
    backend/
      dsl2          the warp-level DSL: operands, tiles, accumulators, pipes, roles
      atom          the layouts the instructions fix, and the deciders that read
                    an encoding back off a layout
      lower2        lowering: copies compiled from both ends' layouts, pipes, roles
      emit          address expressions to instructions
      sched         control words: stalls, scoreboards, wait masks
      sass          the instructions we emit, tcgen05 and TMA included
      test_derive   the derivations against what the device and ptxas use
      node/         sasm.py (assembler driver, ELF writer), run_tma.py (launch, check)
    test/
      test_layouts        the operations and their laws, against enumeration
      test_cute_algebra   CuTe's documented examples of composition, complement, division, product
      test_cutlass_atoms  PTX fragment layouts, GMMA swizzle atoms, the SM90 accumulator derived
                          from the SM80 fragment, a GEMM mainloop built from the operations alone
      test_simplifier     the decision procedure against brute force, and on random layouts
      test_usage_table    every formula of the paper's usage table, built as printed
    paper/

## Build

    dune build
    dune test

## warpc

`backend/` compiles warp-level kernels to SASS for Blackwell (sm_100a)
directly, with no PTX in the path. A kernel is a set of warp roles over shared
tiles, tensor-memory accumulators and mbarrier pipes. Tiles are declared by
shape only: the instruction that consumes a tile fixes its layout, and every
copy is compiled from the layouts of its two ends.

Concretely, for the GEMM below every address the kernel computes, every
descriptor field and every tensor-map box is read off a layout of `lib/`:

- `backend/atom.ml` holds the layouts the instructions fix, as values of the
  algebra: the K-major SWIZZLE_128B operand a UMMA descriptor describes, the
  SWIZZLE_128B image of a tensor-map box, the tensor-memory accumulator, the
  fragment of `tcgen05.ld.32x32b`. Each comes with a decider that reads the
  instruction's encoding back off a layout and compares the image it
  describes with the layout at every coordinate, so a layout the instruction
  cannot express is refused at compile time.
- A copy is the moving instruction's fragment composed with the storage at
  each end. The load from tensor memory is the fragment dealt over the
  accumulator's blocks (`interleave`) composed with the accumulator divided
  into blocks (`divide`); the staging write is the same fragment composed
  with the staging tile's layout. The composites are checked — injective,
  vectors contiguous and aligned, the load's warp-uniform-address contract —
  and their strided forms (`Decide`), or their pipelines sliced at the
  compile-time coordinates (`Restricted`), are what `backend/emit.ml` turns
  into instructions. The CTA-to-tile map is a layout too, emitted from its
  decided strided form.
- The host encodes each tensor map from the `.tmap` lines the kernel emits,
  so it cannot disagree with the addresses the kernel computes.

`backend/test_derive.ml` pins the derivations against what the device and
ptxas use: the derived operand descriptor's high word is `0x40004040`, the word
CUTLASS's mainloop loads; the derived staging addresses are the ones measured
exact on the device.

### A program

The GEMM as written in the DSL (`backend/dsl2.ml`). One warp feeds the ring by
TMA, one drives the tensor core, four write the accumulator out through a
staging tile.

    smem =
      [ { sname = "sa"; sdtype = F16; srows = tile_m; scols = tile_k; ring = Stages }
      ; { sname = "sb"; sdtype = F16; srows = tile_n; scols = tile_k; ring = Stages }
      ; { sname = "sc"; sdtype = F32; srows = 32;     scols = 32;     ring = Per_warp 2 } ]
    ...
    body =
      [ Role ([0],
          [ Kloop [ Wait "empty"
                  ; Tma { dst = "sa"; src = "a";  rows = Tile_m; pipe = "full" }
                  ; Tma { dst = "sb"; src = "bt"; rows = Tile_n; pipe = "full" } ] ])
      ; Role ([1],
          [ Wait "free"
          ; Kloop [ Wait "full"; Mma { d = "acc"; a = "sa"; b = "sb" }; Commit "empty" ]
          ; Commit "ready" ])
      ; Role ([4;5;6;7],
          [ Wait "ready"; Store { dst = "c"; src = "acc"; via = "sc"; release = Some "free" } ]) ]

No statement names a layout. `sa` and `sb` get theirs from the `Mma` that
reads them, `sc` from the tensor-map store that reads it, `acc` from the MMA
that writes it; the `Tma` that fills `sa` and the warps that write `sc` are
compiled against those layouts, and refused if the instruction cannot produce
them.

### Benchmarks

fp16 inputs, fp32 accumulate, one idle B200, 30 iterations each, measured in
one session. CUTLASS is example 70_blackwell_fp16_gemm built from source with
CUDA 12.9. Every warpc result equals numpy's; the inputs are integers in
[-3, 3], so the fp32 sums are exact and equality is the right test for the
addressing, not a statement about rounding.

    shape                warpc     CUTLASS
    1024^3               242.9       247.3
    1536^3               647.2       538.5
    2048^3               972.0      1017.4
    4096^3              1327.2      1513.8
    8192^3              1587.0      1260.2
    16384^3             1639.2      1281.4
    4096x4096x1024       871.1      1056.8
    3072x1280x2048       914.8       959.2
    8192x2048x4096      1373.2      1494.3
                                    TFLOP/s

Ahead at 1536 cubed and from 8192 cubed up, behind elsewhere, by up to 18 per
cent at short K. The shapes where warpc leads are the ones where CUTLASS's
own kernel falls off (1514 at 4096 cubed, 1260 at 8192). The comparison is
not like for like: CUTLASS runs a two-CTA MMA on a 2x2 cluster, which moves
each operand slice once per pair of CTAs; warpc runs one CTA per tile.

### What it is not yet

- One program. The statements are specialised to this GEMM's instructions:
  `Tma` is a 2-D box, `Mma` is f16, K-major, M = 128, `Store` is tensor memory
  to a staging tile to a tensor-map store. Only the 128-byte swizzle is
  supported, each further mode needing its own check on the device.
- No layout conversion. Nothing yet derives the staging and swizzle that
  take one fragment layout to another; the staging tile is declared.
- The schedule is written, not searched. Roles, ring depth, warp assignment
  and the tile-width rule are the program's; registers are a fixed map in
  `lower2.ml`; `sched.ml` keeps program order and decides only stalls,
  scoreboards and wait masks.
- The cluster and two-CTA MMA (`--cluster X Y --pair`) run but are not
  correct: about one value in 10^4 is wrong, in the columns the partner CTA's
  half of B supplies, so the leader is reading that half before it lands.
  CUTLASS's own schedule is therefore not yet transcribed, and the table
  above is not the like-for-like comparison.
- Shapes must be multiples of the tiles (128, and 256 or 128, and 64); there
  is no predication for ragged edges.

### Running one

    dune build && dune test
    ./_build/default/backend/warpc.exe pgemm 4096 4096 4096 4 > k.sass

`warpc` writes SASS with a header naming the launch: registers, shared memory,
grid, cluster, and a `.tmap` line per tensor map. `backend/node/sasm.py`
assembles it into a cubin with cupatch (silares-ai/cupatch) as the encoder,
and `backend/node/run_tma.py` encodes the tensor maps from the header,
launches it, and checks it against numpy.
