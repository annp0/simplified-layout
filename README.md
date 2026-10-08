# layouts

A layout algebra for GPU tensor kernels, in OCaml, and the paper describing it
(`papers/layout-algebra/layout-algebra.tex`).

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
    test/
      test_layouts        the operations and their laws, against enumeration
      test_cute_algebra   CuTe's documented examples of composition, complement, division, product
      test_cutlass_atoms  PTX fragment layouts, GMMA swizzle atoms, the SM90 accumulator derived
                          from the SM80 fragment, a GEMM mainloop built from the operations alone
      test_simplifier     the decision procedure against brute force, and on random layouts
      test_usage_table    every formula of the paper's usage table, built as printed
    rocq/                 the mechanized proofs
    papers/
      layout-algebra/     the paper: layout-algebra.tex inputs sections/ and figures/
      archive/            earlier single-file drafts, kept for reference

## Build

    opam install . --deps-only
    dune build
    dune test

## Mechanized proofs

The paper's lemmas and theorem, the decision procedure as a whole, and what
Section 3 claims of each operation are proved in Rocq under `rocq/`, with no
axioms and no admitted goals:

    (cd rocq && rocq makefile -f _RocqProject -o Makefile && make)
    ./rocq/check.sh      # the mechanized scan vs. Decide.fit_axis

`rocq/check.sh` runs both renderings of the scan over every
`g : [0,n) -> [0,k)` with `g 0 = 0` and checks they accept the same maps
and recover the same shape. See `rocq/README.md` for the correspondence
with the paper and for what is not covered.

## The paper's numbers

Every figure in the paper's evaluation is generated from a run of the test
suite rather than transcribed into the prose:

    ./papers/eval.sh            # rewrite papers/eval-numbers.tex
    ./papers/eval.sh --check    # fail if it is stale (for CI)

Each suite prints one `#eval KEY VALUE` line per figure; the script sums by
key across the suites and writes the `\newcommand`s that
`papers/layout-algebra/layout-algebra.tex` inputs. Both random generators are
seeded, but the random layouts also depend on OCaml's `Random` (which changed
in OCaml 5.0) and on Base's `List.permute`, so a rerun reproduces every number
only with the same toolchain. The committed figures were produced with OCaml
5.2.0 and Base v0.17.3.

## CuTe, measured

`study/` turns the paper's claim about CuTe's admissibility conditions into
a measurement, by compiling CuTe's header-only layout algebra on the host
and checking its complement against the postconditions CuTe's own unit test
asserts:

    CUTLASS_DIR=... CCCL_DIR=... ./study/run.sh           # measure
    CUTLASS_DIR=... CCCL_DIR=... ./study/run.sh --check   # fail if stale

No GPU and no CUDA toolkit are needed --- `study/stub/` supplies the handful
of CUDA declarations the headers include unconditionally. See
`study/README.md`.
