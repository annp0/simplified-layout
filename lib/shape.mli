(** The coordinate domain of a layout: a bound for a single axis,
    or a product of sub-shapes for a tuple of coordinates. *)
type t =
  | Bound of int
  | Product of t list
[@@deriving sexp_of, compare]

(** Total number of coordinates in the domain. *)
val size : t -> int
