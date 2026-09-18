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
      dsl2          the warp-level DSL: operands, stages, accumulators, pipes, roles
      lower2        lowering to registers, barriers, tile mapping
      sched         control words: stalls, scoreboards, wait masks
      sass          the instructions we emit, tcgen05 and TMA included
      node/sasm.py  the assembler driver and ELF writer
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

`backend/` is a compiler for warp-level GPU kernels that emits SASS for
Blackwell (sm_100a) directly, with no PTX in the path. A kernel is a set of
warp roles over a ring of shared-memory stages; the operand addresses come from
the algebra in `lib/`, where a fragment's per-lane address is a composed layout
lowered to shifts and masks.

### A program

The whole GEMM, as written in the DSL (`backend/dsl2.ml`). Three roles: one
warp feeds the ring by TMA, one drives the tensor core, four write the
accumulator out.

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
          [ Wait "ready"; Store { dst = "c"; src = "acc"; release = Some "free" } ])
      ]

The declarations around it name the stages and the handshakes: `sa` and `sb`
are shared-memory tiles held `depth` deep, `acc` is a tensor-memory
accumulator, and `full`, `empty`, `ready`, `free` are mbarriers, one per stage
or per accumulator. The compiler prints what it read back before it emits:

    kernel pgemm_4096_4096_4096_s4_t256 (c : f32[4096,4096], a : f16[4096,4096] via tma, ...)
      tile 128x256, k tile 64, ring depth 4, 8 warps, cluster of 1
      smem sa : f16[128,64] x depth
      smem sb : f16[256,64] x depth
      tmem acc : f32[128,256] x 1 buffers
      pipe full[stage], 1 arrival
      pipe empty[stage], 1 arrival, free at start
      warps 0
        for each k tile (stage = k mod depth)
          wait empty
          sa[stage] <- tma a[tile_m rows, k tile]  -> full
          sb[stage] <- tma bt[tile_n rows, k tile]  -> full
      warps 1
        wait free
        for each k tile (stage = k mod depth)
          wait full
          acc += sa[stage] . sb[stage]^T
          commit empty
        commit ready
      warps 4,5,6,7
        wait ready
        c[tile, rows of warp] <- acc, then free

Everything below that line is ours: the tile-to-CTA map, the TMA descriptors,
the mbarrier phases and their parity, tensor-memory allocation, the epilogue's
swizzled staging and TMA store, register allocation, and the control word on
every instruction.

### Benchmarks

fp16 inputs, fp32 accumulate, one idle B200, 30 iterations. Every warpc result
is bit-exact against numpy. CUTLASS is example 70_blackwell_fp16_gemm built
from source with CUDA 12.9, measured back to back with ours.

    shape                warpc     CUTLASS
    1024^3               245.9       250.4
    1536^3               662.9       543.7
    2048^3               978.6      1009.2
    4096^3              1324.1      1516.9
    8192^3              1585.7      1259.9
    16384^3             1644.0      1281.0
    4096x4096x1024       875.7      1062.4
    3072x1280x2048       890.3       955.2
    8192x2048x4096      1372.8      1492.5
                                    TFLOP/s

We are ahead from 8192 cubed up, by 26 to 28 per cent, and at 1536 cubed by 22.
We are behind at 4096 cubed and at short K. The cause is the schedule, not the
code we emit for it: CUTLASS runs a two-CTA MMA on a 2x2 cluster, so an operand
slice crosses memory once per pair of CTAs rather than once per CTA, which
matters most where operand traffic dominates. That schedule is expressible here
and is being brought up; it is not yet correct, so it is not the default.

### Running one

    dune build
    ./_build/default/backend/warpc.exe pgemm 4096 4096 4096 4 > k.sass

`warpc` writes SASS with a header naming the launch parameters.
`backend/node/sasm.py` assembles it and writes a cubin, using cupatch as the
encoder; the driver loads and launches it.
