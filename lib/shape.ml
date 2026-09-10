open! Base

type t =
  | Bound of int
  | Product of t list
[@@deriving sexp_of, compare]

let rec size = function
  | Bound n -> n
  | Product ts -> List.fold ts ~init:1 ~f:(fun acc t -> acc * size t)
