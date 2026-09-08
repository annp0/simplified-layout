(** Integer address expressions. The emitter produces two kinds and
    nothing else: a STRIDED FORM, [k + sum s_ij * digit_ij(c_i)],
    decided by [Decide]; or, for the maps that have none, the
    composition pipeline written out with one binding per stage, so a
    stage's index is computed once and its digits read off it.

    There is no rewrite system here. Recovering a strided form by
    rewriting is both incomplete and, off the strided class,
    counterproductive: it inlines a shared stage index into every digit
    and splits the digits apart. Deciding is complete and the pipeline
    is smaller, so the two together leave rewriting nothing to do.
    Constant folding is all that remains. *)

type t =
  | Const of int
  | Var of string
  | Sum of (int * t) list * int (** coefficient * term, plus constant *)
  | Div of t * int
  | Mod of t * int
  | Xor of t * t
  | Let of string * t * t (** [Let (x, e, body)]: [e] computed once *)
[@@deriving sexp_of, compare]

val var : string -> t

(** Constructors fold constants and merge like terms. *)

val add : t -> t -> t
val scale : int -> t -> t
val sum : t list -> t
val div : t -> int -> t
val modulo : t -> int -> t
val xor : t -> t -> t
val bind : string -> t -> t -> t

(** No division, modulus, or exclusive-or anywhere: a single affine
    combination of the coordinate variables. *)
val is_affine : t -> bool

val eval : t -> (string -> int) -> int

(** Replace the variables the function maps to [Some v] by constants,
    folding as it goes. *)
val subst : t -> (string -> int option) -> t

val to_string : t -> string
