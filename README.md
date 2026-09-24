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

The GEMM as written in the DSL (`backend/dsl2.ml`), in the configuration
`warpc gemm` chooses from 8192 cubed up. One warp feeds the ring by TMA, one
drives the tensor core, four write the accumulator out, one takes tiles by
cluster launch control.

    atom = Atom.umma ~ab:F16 ~acc:F32 ~m:256 ~n:256 ~ctas:2
             ~a_major:K_major ~b_major:K_major ~a_src:Smem_desc
    (* each CTA stages the rows of each operand the atom gives it; A holds
       the rows of both blocks the MMA stacks along M *)
    smem =
      [ { sname = "sa"; sdtype = F16; srows = rows_of (Atom.umma_b atom); scols = 64; ring = Stages }
      ; { sname = "sb"; sdtype = F16; srows = 2 * rows_of (Atom.umma_a atom); scols = 64; ring = Stages }
      ; { sname = "sc"; sdtype = F32; srows = 8; scols = 32; ring = Per_warp 2 } ]
    tmem = [ { tname = "acc"; trows = 128; tcols = 256; reps = 2; bufs = 1 } ]
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
          [ Wait "ready"; Store { dst = "c"; src = "acc"; via = Some "sc"; release = Some "free" } ])
      ; Role ([2], [ Schedule ]) ]

This is cuBLAS's `nvjet_hss_256x256_64x4_2x1_2cta` as the DSL states it. No
statement names a layout. `sa` and `sb` get theirs from the `Mma` that reads
them, and the atom says how many of their rows each CTA of the pair stages;
`sc` gets its layout from the tensor-map store that reads it, `acc` from the
MMA that writes it. The MMA's A operand is the tile of `bt`, so the
accumulator's lanes run along the output's columns, and the store composes
the load's fragment with a transpose. `via = None` stores each warp's
registers straight to C instead, one 128-byte store per register.

### Benchmarks

fp16 inputs, fp32 accumulate, one B200. warpc runs the configuration
`warpc gemm` chooses for the shape (below). cuBLAS is cuBLASLt 12.9 on the
same problem (A row-major, B^T row-major, fp32 C, alpha 1, beta 0); in the
first round every algorithm its heuristic returns is run and the fastest exact
one is kept for the next two. The time is each kernel's device time from nsys,
the median of 100 launches back to back. The two alternate on the same GPU for
three rounds and the table gives the medians. Launch overhead is not in these
numbers, for either library. Every warpc result equals numpy's and every
cuBLAS result is checked exactly on sampled entries; the inputs are integers
in [-3, 3], so the fp32 sums are exact and equality tests the addressing, not
rounding.

The ceiling is measured with every SM issuing back-to-back M = 128 tcgen05
MMAs out of shared memory, with no loads and no epilogue. That completes 8192
FLOP per clock, and at the 1852 MHz the GPU holds under that load 148 SMs give
2243 TFLOP/s.

    shape                  warpc      cuBLAS    warpc   cuBLAS  warpc  cuBLAS   warpc
                                                TFLOP/s TFLOP/s of peak of peak faster
    1024^3               4256 ns     4912 ns    504.6    437.2    22%    19%  +15.4%
    1536^3               7520 ns     8160 ns    963.8    888.2    43%    40%   +8.5%
    2048^3              14.05 us    14.05 us   1222.9   1222.9    55%    55%    0.0%
    4096^3              74.91 us    75.18 us   1834.7   1828.0    82%    81%   +0.4%
    4096x4096x1024      25.98 us    26.10 us   1322.3   1316.7    59%    59%   +0.4%
    3072x1280x2048      13.65 us    14.05 us   1180.1   1146.5    53%    51%   +2.9%
    8192x2048x4096      74.80 us    76.11 us   1837.4   1805.7    82%    81%   +1.8%
    8192^3             543.86 us   558.14 us   2021.7   1969.9    90%    88%   +2.6%
    16384^3              4.857 ms    4.725 ms  1810.8   1861.7    81%    83%   -2.7%

cuBLAS's kernels are NVIDIA's nvjet kernels, all two-CTA, on clusters of 2, 4
or 8. Every configuration below is a transcription of one, read from its SASS
and from the control words of its binary (captured through CUPTI's
module-load callback), except the pair on 128 x 128 tiles, which came from
CUTLASS's example. The configurations `warpc gemm` chooses:

- **256 x 256 a CTA** when every dimension is 8192 or more
  (`nvjet_hss_256x256_64x4`). An M = 256, N = 256 two-CTA MMA stacked twice
  along M, both operands' tiles of 64 columns of K, ring depth 4, one
  512-column accumulator, tiles by cluster launch control, and the tensor-core
  warp asking about the next stage before it issues this stage's MMAs.
- **128 x 192** when 256-row tiles still fill the machine
  (`nvjet_hss_128x192_64x7`). The same with N = 192 and ring depth 7, by
  cluster launch control once K is 4096 or more and on a fixed grid below it.
- **64 x 128, the M = 128 pair** when 128 x 128 tiles would fill at most half
  the machine (`nvjet_hss_64x128_64x13`). Each CTA holds 64 rows of the result
  in CuTe's 2x2 tensor-memory layout, ring depth 13, and each warp stores its
  registers straight to C.
- **128 x 128 on 2x2 or 2x4 clusters** when those tiles take more than one wave
  (`nvjet_hss_128x128_64x9_2x2` and `_2x4`). The pairs of a cluster share the
  tile of B^T, each CTA loading a slice of it and multicasting it to the
  others; the wider cluster is taken when it needs no more waves.
- **The pair on CUTLASS's orientation**, 128 x 128 a CTA on a 2x1 cluster,
  ring depth 8, otherwise (1536 cubed).

What the transcription needed that is not in any documentation, each found on
the B200 and each now enforced by the lowering:

- A uniform register a barrier operation names must hold that barrier's
  address for the whole kernel; a barrier addressed at run time goes through
  a general register, as ptxas does it.
- The cluster-launch-control answer must be read by one 128-bit load.
- A failed barrier test must sleep (`NANOSLEEP.SYNCS`) before trying again, or
  the two-CTA kernel at ring depth 7 hangs in most launches.
- UTCHMMA reads its descriptor registers late. It may issue 9 cycles after the
  add that wrote them and 2 after the previous MMA, as nvjet issues it; 6
  cycles after the add, it reads the old descriptor.
- Barrier initialisations need not wait for one another. The cluster's arrival
  waits for all of them, which is what ptxas makes of
  `fence.mbarrier_init`; chaining them cost 300 ns of every prologue.
- A CTA may leave without meeting its cluster once every stage and accumulator
  it handed out has come back, the pair's accumulator release going to the
  leader alone. The cluster barrier at exit cost 600 ns.
- A B200 holds 74, 33 and 15 clusters of 2, 4 and 8 CTAs at once, not 148
  divided by the cluster size.

### What it is not yet

- Faster than cuBLAS at 16384 cubed. Its 256 x 256 kernel is 2.7 per cent
  ahead there with the same instructions, the same ring and the same
  epilogue; at 8192 cubed the same transcription is 2.6 per cent ahead of it.
  The tensor maps, the tile walk, the order of the MMAs and the epilogue's
  store path have each been ruled out by measurement.
- Faster at 2048 cubed. Both take two tiles a multiprocessor on 1.7 tiles of
  work; removing that needs a split of K across CTAs (stream-K), which the DSL
  cannot yet express.
- One program. The statements are specialised to this GEMM's instructions:
  `Tma` is a 2-D box, the atom is kind::f16 with K-major operands from shared
  memory, and only the 128-byte swizzle is supported, each further mode
  needing its own check on the device.
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
[--tile-m M] [--bufs B] [--cluster X Y] [--pair] [--swap] [--clc]
[--ask-ahead] [--direct]` states it (`--swap`: the MMA's A operand is the tile
of B^T; `--clc`: tiles by cluster launch control; `--ask-ahead`: the
tensor-core warp asks about the next stage before this stage's MMAs;
`--direct`: each warp stores its registers straight to C). `--stamps` and
`--stage-stamps` build a kernel that writes the global timer at each phase
boundary, or at each stage; `--debug-waits` one whose waits give up after a
bounded spin and report which they were. The output is SASS with a header
naming the launch: registers, shared memory, grid, cluster, and a `.tmap`
line per tensor map (`.ptr` for a plain pointer). `backend/node/sasm.py` assembles it into a cubin
with cupatch (silares-ai/cupatch) as the encoder; `backend/node/run_tma.py`
encodes the tensor maps from the header, launches it, checks it against
numpy and times it.
