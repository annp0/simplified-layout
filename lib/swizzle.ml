open! Base

type t =
  { bits : int
  ; src : int
  ; dst : int
  }
[@@deriving sexp_of, compare]

let validate ({ bits; src; dst } as t) =
  if bits < 1 || src < 0 || dst < 0 || not (src + bits <= dst || dst + bits <= src)
  then
    raise_s
      [%message
        "Swizzle.validate: bit fields must be well-formed and disjoint" (t : t)]
;;

let eval { bits; src; dst } x = x lxor (((x lsr src) land ((1 lsl bits) - 1)) lsl dst)
