(** A point in a coordinate domain: an index into a single axis,
    or a tuple of coordinates, one per component of a product shape. *)
type t =
  | Idx of int
  | Tuple of t list
[@@deriving sexp_of, compare]

(** [fits t shape] is [true] iff [t] has the structure of [shape]
    and every index is within its bound. *)
val fits : t -> Shape.t -> bool

(** [unflatten shape i] decodes a canonical (row-major) linear index
    into the coordinate of [shape] it stands for — the inverse of
    evaluating [Linear.canonical shape]. Raises if [i] is out of range.
    This function IS the convention that lets an [int] mean a position
    in a logical space. *)
val unflatten : Shape.t -> int -> t

(** All coordinates of [shape], in canonical order. *)
val enumerate : Shape.t -> t list

(** A coordinate with holes, for restricting a layout's domain:
    [At i] fixes a slot, [Free] keeps it (and its whole subtree),
    [Parts] recurses into a tuple. *)
type partial =
  | Free
  | At of int
  | Parts of partial list
[@@deriving sexp_of, compare]
