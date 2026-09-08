# layouts

A layout algebra for GPU tensor kernels, in OCaml, and the paper describing it.

A layout maps coordinates of a tile to integers. Here every layout also names
the space its input and output live in — a logical index, a thread-value index,
or a physical offset — and what a layout must satisfy follows from that:

- into logical or thread-value space, a dense bijection;
- into physical space, alias-free, with injectivity required of store targets;
- nothing maps out of a physical offset.

Composition asks only that the first map cover the second's domain exactly. The
composite is kept as the pair rather than fused, so no divisibility conditions
arise. Whether the composite is itself a layout, over a possibly finer shape,
is then decided rather than assumed: `Decide.strided_form` returns that layout
when one exists and `None` when none does, in `O(size)` evaluations plus work
linear in each axis.

## Layout

    lib/          the algebra
      space.mli     the three index spaces
      shape, coord  shapes, coordinates, flattening
      linear        strides and replication
      swizzle       the physical-to-physical bijection
      layout        layouts, composition, emission
      restricted    slices, kept as data beside an unmodified layout
      decide        is this map a layout? the decision procedure
      expr          the emitted integer expressions
    test/         four suites
    paper/        layout-algebra.tex

## Build

    dune build
    dune test

The suites check CuTe's own worked examples, transcribed hardware atoms with
PTX spot checks, a GEMM mainloop derived from the operations alone, and an
oracle that evaluates every emitted expression at every coordinate against the
map it came from.
