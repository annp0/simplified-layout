open! Base

type t =
  | Idx of int
  | Tuple of t list
[@@deriving sexp_of, compare]

let rec fits t (shape : Shape.t) =
  match t, shape with
  | Idx i, Bound n -> 0 <= i && i < n
  | Tuple cs, Product ss ->
    (match List.for_all2 cs ss ~f:fits with
     | Ok b -> b
     | Unequal_lengths -> false)
  | Idx _, Product _ | Tuple _, Bound _ -> false
;;

let unflatten (shape : Shape.t) i =
  if i < 0 || i >= Shape.size shape
  then raise_s [%message "Coord.unflatten: index out of range" (i : int) (shape : Shape.t)];
  let rec go (shape : Shape.t) i =
    match shape with
    | Bound _ -> Idx i
    | Product ss ->
      (* row-major: the last component varies fastest, so peel components
         off from the right *)
      let coords, _ =
        List.fold (List.rev ss) ~init:([], i) ~f:(fun (acc, i) s ->
          let n = Shape.size s in
          go s (i % n) :: acc, i / n)
      in
      Tuple coords
  in
  go shape i

let enumerate shape = List.init (Shape.size shape) ~f:(unflatten shape)

type partial =
  | Free
  | At of int
  | Parts of partial list
[@@deriving sexp_of, compare]
