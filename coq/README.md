# Mechanized proofs

Coq 8.19 proofs of the paper's two theorems. Everything is proved: no
`Admitted`, no `Axiom`, and `Print Assumptions` reports *Closed under the
global context* for each main result.

    make                # build (needs a switch with Coq)
    ./check.sh          # compare the mechanized scan with the OCaml one

## What is proved

| Paper | Coq | File |
|---|---|---|
| Lemma 1 (dense bijections) | `dense_iff_running` | `Dense.v` |
| Lemma 3 (digits as differences of floors) | `dgsum_fsum` | `Chain.v` |
| Theorem 1 (linear recognition) | `scan_iff`, `scan_sound_layout` | `Complete.v`, `Shape.v` |

**Lemma 1**, both directions:

```coq
Theorem dense_iff_running (L : modes) :
  sizes_ge2 L -> strides_pos L -> sorted_strides L ->
  (Dense 1 L <-> running 1 L).
```

`Dense 1 L` says the index function is a bijection from the coordinates
onto `[0, N)`; `running 1 L` says the strides are the running products
of the sizes. Stated for modes already sorted by stride, which is where
the content is — sorting permutes the modes, and permuting modes
permutes the coordinates without changing the image or injectivity.

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

and, on the accepting side, as a statement about layouts rather than
about floor sums:

```coq
Theorem scan_sound_layout (n : nat) (g : nat -> Z) (ws : list (nat * Z)) :
  (1 <= n)%nat -> g 0%nat = 0 -> scan n g = Some ws ->
  let T := shape_of_chain n ws in
  wf T /\ tsize T = n /\ nof T = n
  /\ forall v, (v < n)%nat -> g v = dgsum T v.
```

## Two places where the formalization is deliberately not the paper

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

## Agreement with the implementation

`check.sh` runs `Recognize.scan` (Coq) and `Decide.fit_axis` (OCaml)
over every `g : [0,n) -> [0,k)` with `g 0 = 0`, for the parameters the
paper's evaluation uses. They accept the same maps and recover the same
shape:

| n | k | maps | accepted (Coq) | accepted (OCaml) |
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
accepted. That case is left out of the Coq column because `nat` is
unary and `vm_compute` over 177,147 maps is slow; extraction would be
the way to include it.

## Not mechanized

- **The coarsest-chain claim.** Theorem 1 also says every accepting
  shape's chain contains the one the scan finds. `scan_iff` gives the
  equivalence but not this minimality. The OCaml tests check it against
  a brute-force search over divisor chains (`test_simplifier.ml`).
- **`s_j = g(w_j)`**, the last clause of Lemma 3. `Shape.shape_of`
  builds the strides from the coefficients by the change of variables,
  which is what the bridge lemma needs; that these equal `g` at the
  weights is proved in the paper but not here.
- **Separability** (the paper's Lemma 2) and everything above the
  per-axis question: the mechanization covers one coordinate at a time,
  which is the part with the theorem in it.
- **Mode permutation** for Lemma 1, as noted above.
