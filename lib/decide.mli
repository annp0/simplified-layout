(** The strided form of an address map, DECIDED rather than searched
    for.

    A map's domain is a finite box, so every value is available, and the
    question "is this map a layout whose shape refines the domain
    shape?" is answered by evaluation:

    - SEPARABILITY. Every digit of a refinement belongs to one axis, so
      a strided form is [k + sum_i g_i(c_i)] with [g_i v = f (v e_i) - f 0]
      forced. One pass over the box settles it.
    - PER AXIS, in linear time. A digit is a difference of floor terms,
      so a strided form of [g_i] is a weighted sum of [v / w] over a
      chain of divisors of [n_i]. First differences turn each [v / w]
      into the indicator of the multiples of [w], so scanning upwards
      forces one weight and one coefficient at a time. A form exists
      exactly when the weights so forced divide [n_i] and form a
      divisibility chain.

    The forced weights are necessary and, with weight 1 --- which every
    refinement carries, since its digits must cover the axis --- they are
    the weights of the COARSEST refinement; an affine map yields a plain
    affine sum. A [None] is a proof that no strided form exists over any
    refinement. Cost is [O(size)] evaluations for separability and
    [O(n_i)] per axis: no factorization, no search.

    The characterization these rules rest on --- digits as differences of
    floor terms, first differences as indicators of divisibility, and
    the coefficients they force --- is also that of Appendix A.2.1 of
    Axe (Hou et al., arXiv:2601.19092), which uses it to prove a
    normalized representation unique. What is different here is the
    question: an arbitrary map on a finite box, existence decided rather
    than assumed, in linear time, with a pipeline to fall back on when
    the answer is no. *)

val strided_form : shape:Shape.t -> offset:(Coord.t -> int) -> Expr.t option

(** The per-axis recognizer, exposed for testing against a brute-force
    search over divisor chains: [(radix, weight, price)] per digit,
    coarsest first, or [None]. *)
val fit_axis : (int -> int) -> n:int -> (int * int * int) list option
