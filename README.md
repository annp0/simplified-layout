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
- The MMA is a value too: `Atom.umma` is CuTe's `SM100_MMA_F16BF16_SS` /
  `_2x1SM_SS` -- operand and accumulator types, M x N over the CTAs it spans,
  its cta_group, the operands' majors and where each is read from -- with the
  shapes CuTe accepts and CuTe's A, B and C thread-value layouts. The rows of
  each operand a CTA stages, the rows of the result it holds, the K step and
  the 32-bit instruction descriptor (field by field, as
  `UMMA::InstrDescriptor`) are read off it.
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

    atom = Atom.umma ~ab:F16 ~acc:F32 ~m:256 ~n:256 ~ctas:2
             ~a_major:K_major ~b_major:K_major ~a_src:Smem_desc
    (* each CTA stages the rows of each operand the atom gives it *)
    smem =
      [ { sname = "sa"; sdtype = F16; srows = rows_of (Atom.umma_b atom); scols = 64; ring = Stages }
      ; { sname = "sb"; sdtype = F16; srows = rows_of (Atom.umma_a atom); scols = 64; ring = Stages }
      ; { sname = "sc"; sdtype = F32; srows = 8; scols = 32; ring = Per_warp 2 } ]
    ...
    body =
      [ Role ([0],
          [ Kloop [ Wait "empty"
                  ; Tma { dst = "sa"; src = "a";  rows = Tile_m; pipe = "full" }
                  ; Tma { dst = "sb"; src = "bt"; rows = Tile_n; pipe = "full" } ] ])
      ; Role ([1],
          [ Wait "free"
          ; Kloop [ Wait "full"; Mma { atom; d = "acc"; a = "sb"; b = "sa" }; Commit "empty" ]
          ; Commit "ready" ])
      ; Role ([4;5;6;7],
          [ Wait "ready"; Store { dst = "c"; src = "acc"; via = "sc"; release = Some "free" } ])
      ; Role ([2], [ Schedule ]) ]

This is cuBLAS's `nvjet_hss_128x256_64x6_2x1_2cta` (8192 cubed) as the DSL
states it. No statement names a layout. `sa` and `sb` get theirs from the
`Mma` that reads them, and the atom says how many of their rows each CTA of
the pair stages; `sc` gets its layout from the tensor-map store that reads it,
`acc` from the MMA that writes it. Because the MMA's A operand is the tile of
`bt`, the accumulator's lanes run along the output's columns: the store
composes the load's fragment with a transpose and the staging tile becomes
8 x 32 f32 boxes, written by single-element stores at nvjet's addresses.
`Schedule` is the role that takes tiles by cluster launch control; every other
role reads its answers.

### Benchmarks

fp16 inputs, fp32 accumulate, one B200. warpc runs the configuration
`warpc gemm` chooses for the shape (below). CUTLASS is example
70_blackwell_fp16_gemm built from source with CUDA 12.9, as shipped; its timed
loop calls `gemm.initialize` on the host before every `gemm.run`, so its times
include that call. cuBLAS is cuBLASLt 12.9 on the same problem (A row-major,
B^T row-major, fp32 C, alpha 1, beta 0): every algorithm its heuristic returns
is timed and the fastest exact one is given. The three alternate on the same
GPU, three rounds, 50 iterations a round, timed between CUDA events on the
device; the table gives the medians. Every warpc result equals numpy's and
every cuBLAS result is checked exactly on sampled entries; the inputs are
integers in [-3, 3], so the fp32 sums are exact and equality tests the
addressing, not rounding.

The ceiling is measured the same way: every SM issuing back-to-back
M = 128 tcgen05 MMAs out of shared memory, with no loads and no epilogue,
completes 8192 FLOP per clock; at the 1852 MHz the GPU holds under that load,
148 SMs give 2243 TFLOP/s.

    shape                warpc    CUTLASS     cuBLAS    warpc    cuBLAS
                                  example              of peak  of peak
    1024^3               317.9      253.9      345.1      14%      15%
    1536^3               693.1      550.8      703.6      31%      31%
    2048^3              1009.9      988.4     1043.9      45%      47%
    4096^3              1666.4     1509.6     1720.7      74%      77%
    4096x4096x1024      1108.8     1055.2     1194.5      49%      53%
    3072x1280x2048       953.0      967.4      979.1      42%      44%
    8192x2048x4096      1673.3     1481.6     1707.6      75%      76%
    8192^3              1964.9     1253.6     1969.6      88%      88%
    16384^3             1834.0     1268.6     1933.8      82%      86%
                                    TFLOP/s

cuBLAS's kernels are NVIDIA's nvjet kernels, not CUTLASS's: all two-CTA, on a
cluster of 2, 4 or 8, tiles taken by cluster launch control. From 4096 cubed up
warpc runs transcriptions of them, read from their SASS through ncu; it
matches cuBLAS at 8192 cubed and is within 2 to 7 per cent at the other large
shapes. The CUTLASS example is behind warpc everywhere but 3072x1280x2048. The
configurations `warpc gemm` chooses:

- **nvjet's 128x256, cluster launch control**, when every dimension is 8192
  or more: a 2x1 cluster, an M = 256, N = 256 two-CTA MMA whose A operand is
  the tile of B^T, ring depth 6, two 256-column accumulators, the epilogue in
  8-row chunks of the transposed accumulator, and a scheduler warp cancelling
  unlaunched clusters and handing their tiles to every role of its cluster.
- **nvjet's 128x192, a fixed grid**, when 256-row tiles still fill the machine
  otherwise: the same with N = 192 (a 96-row share of A per CTA, partial tiles
  at the edges) and ring depth 7. Cluster launch control is slower here
  (4096^3 1634, 8192x2048x4096 1625): each scheduler fills both slots of its
  ring at once, and with five tiles a CTA the tiles it holds at the end cost
  more than the balance gains.
- **The two-CTA pair on CUTLASS's orientation.** An M = 256, N = 128 MMA over
  a 2x1 cluster, 128 x 128 per CTA, ring depth 8, persistent. It is not
  CUTLASS's program either: theirs is a 2x2 cluster, cluster launch control,
  four 128-column accumulator stages, an alpha/beta epilogue in 128 x 16
  subtiles, and a column-major D.
- **One CTA per 128 x 64 tile** when 128-wide tiles would fill at most half the
  machine: the kernel is latency there, and twice the multiprocessors win.

Three device facts the transcription needed, each found by bisection on the
B200 and each now enforced by the lowering: a uniform register a barrier
operation names must hold that barrier's address for the whole kernel (a
barrier addressed at run time goes through a general register, as ptxas does
it); the cluster-launch-control answer must be read by one 128-bit load; and a
failed barrier test must sleep (`NANOSLEEP.SYNCS`) before trying again, or the
two-CTA kernel at ring depth 7 hangs in most launches.

### What it is not yet

- The rest of nvjet. cuBLAS's kernels at 1024 to 3072 and at 4096x4096x1024
  use 2x2 and 2x4 clusters in this orientation (the shared operand
  multicast), at 1024 cubed an M = 128 two-CTA MMA with 64 accumulator lanes a
  CTA, and at 16384 cubed two MMAs a CTA along M (`256x256_64x4`); none is
  expressible yet, so those shapes run the configurations above.
- One program. The statements are specialised to this GEMM's instructions:
  `Tma` is a 2-D box, the atom is kind::f16 with K-major operands from shared
  memory, `Store` is tensor memory to a staging tile to a tensor-map store.
  Only the 128-byte swizzle is supported, each further mode needing its own
  check on the device.
- No layout conversion. Nothing yet derives the staging and swizzle that
  take one fragment layout to another; the staging tile is declared.
- The schedule is written, not searched. Roles, ring depth and warp
  assignment are the program's, and `warpc gemm` picks among measured
  configurations by a rule fitted to the measurements above; registers are a
  fixed map in `lower2.ml`; `sched.ml` keeps program order and decides only
  stalls, scoreboards and wait masks.

### Running one

    dune build && dune test
    ./_build/default/backend/warpc.exe gemm 4096 4096 4096 > k.sass
    python3 backend/node/run_tma.py k.sass

`warpc gemm` picks the configuration; `warpc pgemm M N K DEPTH [TILE_N]
[--tile-m M] [--bufs B] [--cluster X Y] [--pair] [--swap] [--clc]` states it
(`--swap`: the MMA's A operand is the tile of B^T; `--clc`: tiles by cluster
launch control; `--debug-waits`: every wait gives up after a bounded spin and
reports which it was). The output is SASS with a
header naming the launch: registers, shared memory, grid, cluster, and a
`.tmap` line per tensor map. `backend/node/sasm.py` assembles it into a cubin
with cupatch (silares-ai/cupatch) as the encoder; `backend/node/run_tma.py`
encodes the tensor maps from the header, launches it, checks it against
numpy and times it.
