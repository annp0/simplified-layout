# Mechanized proofs

Rocq proofs of the paper's lemmas and theorem, of the decision procedure as
a whole, and of what Section 3 claims of each operation. Everything is
proved: no `Admitted`, no `Axiom`, and `Print Assumptions` reports *Closed
under the global context* for each main result. Checked with Rocq 9.0.1 and
9.1.1.

    rocq makefile -f _RocqProject -o Makefile && make   # build
    ./check.sh          # compare the mechanized scan with the OCaml one
    ./extract.sh        # regenerate extracted/ (--check: fail if stale)

The scripts take Rocq from the current environment, or from the opam switch
named by `ROCQ_SWITCH`.

## What is proved

| Paper | Rocq | File |
|---|---|---|
| Lemma 1 (dense bijections) | `dense_iff_running_general` | `Dense.v`, `DenseSort.v` |
| Lemma 2 (separability) | `separable_iff` | `Separable.v` |
| Lemma 3 (digits as differences of floors) | `dgsum_fsum`, `dgsum_at_weight` | `Chain.v`, `Coarsest.v` |
| Theorem 1 (linear recognition) | `scan_iff`, `scan_sound_layout`, `scan_coarsest`, `scan_strides` | `Complete.v`, `Shape.v`, `Coarsest.v` |
| The whole of `Decide.strided_form` | `decide_iff` | `Decide.v` |
| Nested shapes are their leaves, regrouped | `cleaves_onto`, `cleaves_inj`, `nev_flat`, `nflat_flat` | `Nested.v` |
| `canonical`, `split`, `divide` | `canonical_dense`, `split_correct`, `divide_correct`, `divide_onto`, `divide_inj` | `Ops.v` |
| `repeat`, `interleave` | `repeat_dense`, `interleave_dense`, `cosize_dense` | `Ops.v` |
| `broadcast` | `broadcast_valid`, `broadcast_not_write_valid` | `Ops.v` |
| `inverse` | `inverse_left`, `inverse_right`, `inverse_dense` | `Inverse.v` |
| Swizzles (Definition 4, and under `repeat`) | `swizzle_involutive`, `swizzle_inj`, `swizzle_repeat` | `Swizzle.v` |

**`decide_iff` is the headline.** It is about the checks the
implementation actually runs — separability in one pass, then the scan on
each axis — and says they succeed exactly when the map is the index
function of a layout over a refinement of its domain, plus a constant:

```coq
Theorem decide_iff (S : list nat) (f : list nat -> Z) :
  sizes_pos S ->
  (IsRefined S f <-> Separable S f /\ AllAccept S (axis_gs S f)).
```

`decide_sound` is the half that stops a wrong address formula being
emitted; `decide_complete` is the half that makes "decided, not searched"
true — no simplification is missed.

**Lemma 1**, as the paper states it — drop the modes of size 1, sort the
rest by stride:

```coq
Theorem dense_iff_running_general (L : modes) :
  sizes_pos L -> strides_pos L ->
  (Dense 1 L <-> running 1 (sort_modes (drop_ones L))).
```

`Dense 1 L` says the index function is a bijection from the coordinates
onto `[0, N)`; `running 1 L` says the strides are the running products
of the sizes. The core, `Dense.dense_iff_running`, is stated for modes
already sorted with every size at least two; `DenseSort.v` removes both
assumptions: permuting the modes permutes the coordinates without changing
the image or injectivity (`dense_perm`), a mode of size 1 contributes
nothing (`dense_drop_ones`), and `dense_iff_running_perm` holds against any
sorted arrangement, not only the one `sort_modes` builds. `strides_pos` is
the algebra's own rule: a zero stride is rejected, replication is `⊥`.

The forward direction replaces the paper's counting step ("those modes
produce at most `N_{j-1}` values") with `alignment`: disjoint blocks of
`n` consecutive positions covering `[0, M)` are the aligned ones.
Covering comes from surjectivity and disjointness from injectivity, so
no cardinality argument is needed.

**Theorem 1**, as an "if and only if":

```coq
Theorem scan_iff (n : nat) (g : nat -> Z) :
  (1 <= n)%nat -> g 0%nat = 0 ->
  (exists ws, chain_ok 1 1 n ws /\ Represents n g ws)
  <-> (exists ws', scan n g = Some ws').
```

on the accepting side as a statement about layouts (`scan_sound_layout`),
and with its last two claims about the shape `T` the scan builds:
it is the coarsest — every flat shape of size `n` of which `g` is a
layout has a chain containing `T`'s —

```coq
Theorem scan_coarsest (n : nat) (g : nat -> Z) ws T :
  (1 <= n)%nat -> g 0%nat = 0 -> scan n g = Some ws ->
  wf T -> tsize T = n -> nof T = n ->
  (forall v, (v < n)%nat -> g v = dgsum T v) ->
  incl (weights (shape_of_chain n ws)) (weights T).
```

and its strides are `s_j = g (w_j)` (`scan_strides`). Both rest on
`Complete.scan_exact`: the scan's output is determined by any chain that
represents `g` — it is that chain's entries with nonzero coefficient.

**Section 3.** `canonical S` is Definition 1's row-major flattening and
a dense bijection; `split (n:d) S` is `n:d` read through it; `divide L S`
is `L` precomposed with `(t_i, b_i) |-> b_i k_i + t_i`, a bijection of
coordinates; `repeat` (with the cosize of `L`, which for a dense
bijection is its size) and `interleave` give dense bijections from dense
bijections; `broadcast` is valid but not write-valid; `inverse` and `L`
are mutually inverse as maps on `[0, N)` and `inverse L` is again a dense
bijection; a swizzle with disjoint fields is an involution, and when the
cosize is `2^p` with both fields below `p` it commutes with `repeat`'s copy
offset. These are stated on flat layouts, which `Nested.v` shows loses
nothing.

## Places where the formalization is deliberately not the paper

**The scan does not mutate.** The paper keeps a copy `rho` of the first
difference and subtracts from its multiples. Here the residual is
recomputed from the committed list (`Recognize.resid`). That is the same
number at every step — it is the paper's own invariant — and it avoids
modelling the mutation. `Complete.run` is the identical recursion with
its state exposed, which is what the completeness induction needs.

**Weight 1 is forced into the chain.** `nof T` (the top weight times the
top radix) telescopes to `n` whatever the chain is, so it is *not* the
size of the shape: with chain `w_1 | ... | w_k | n` the radices multiply
to `n / w_1`. `tsize` is the real size, and `Shape.with_one` puts weight
1 in the chain so that the two agree. This mirrors `boundaries = ref
[ 1 ]` in the OCaml `Decide.fit_axis`, and the case it exists for is the
one the OCaml comment names: for `g v = v / 2` on `n = 4` the scan
reports only weight 2, and the shape is `(2, 2)` with strides `(0, 1)`.

**`inverse` assumes every size is at least two**, as Lemma 1's core does:
a mode of size 1 is dropped beforehand.

## Extraction

`Recognize.scan` and `Shape.shape_of_chain` are extracted to OCaml
(`extracted/`, regenerated by `./extract.sh`, checked by
`./extract.sh --check`) and run against `Decide.fit_axis` by
`test/test_extracted.ml` over every `g : [0,n) -> [0,k)` with `g 0 = 0`
for the paper's parameters. On all **186,293** maps the two agree on the
verdict and, on the 58 they accept, on the digits — the check `check.sh`
cannot make, because `nat` is unary and `vm_compute` over the `n = 12`
case (177,147 maps) is too slow inside Rocq. Extracted, it takes 80 ms.

The extraction is **faithful**: no `Extract Inductive` remapping, so `nat`
stays unary and `Z` stays Rocq's binary integers. Remapping `nat` to
OCaml's `int` is the usual trick and would be faster, but it is an
unproved assumption about overflow. The numbers here are axis sizes and
strides, so the cost of not making it is nil.

The extracted code is checked in, because Rocq lives in a different opam
switch from the project's OCaml deps and `dune build` must not need it.

## Agreement with the implementation

`check.sh` runs `Recognize.scan` (Rocq) and `Decide.fit_axis` (OCaml)
over every `g : [0,n) -> [0,k)` with `g 0 = 0`, for the parameters the
paper's evaluation uses. They accept the same maps and recover the same
shape:

| n | k | maps | accepted (Rocq) | accepted (OCaml) |
|---|---|---|---|---|
| 2 | 5 | 5 | 5 | 5 |
| 3 | 5 | 25 | 3 | 3 |
| 4 | 5 | 125 | 15 | 15 |
| 6 | 3 | 243 | 7 | 7 |
| 8 | 3 | 2,187 | 10 | 10 |
| 9 | 3 | 6,561 | 3 | 3 |

and on `g v = v / 2` at `n = 4` both give digits
`(weight 1, radix 2, stride 0), (weight 2, radix 2, stride 1)`.

The OCaml side additionally covers `n = 12, k = 3` (177,147 maps, 15
accepted), which with the rows above is the paper's 186,293 maps and 58
accepted. That case is left out of the Rocq column because `nat` is
unary and `vm_compute` over 177,147 maps is slow; the extracted scan
covers it instead.

## Radix-1 digits

A chain's weights strictly increase, so a shape carrying a radix-1 digit
is not a chain. Such a digit is identically zero — `(v / w) mod 1 = 0` —
so `Decide.drop1` removes it, and the chain reconnects because the weight
the dropped entry would have contributed is its predecessor's. `wf`,
`tsize` and `nof` all survive (`nof` only when something survives at all;
if nothing does then every radix was 1, so the axis has size 1 and the
scan accepts it with no digits, which is what `Decide.fit_axis`
short-circuits to for `n = 1`).

## Not mechanized

- **Section 6**, the correspondence between this algebra's operations and
  CuTe's (the complement as the rest of a `divide`, the product as
  `repeat`, the usage table). The tests check it on CuTe's documented
  examples and CUTLASS's atoms.
- **Section 5**, restriction, whose claims are arithmetic on the slice;
  the tests check its examples.
- **The implementation** beyond the scan: the OCaml operations and
  emitter are checked by the tests against enumeration, not proved.
