open! Base

type t =
  | Axis of
      { size : int
      ; stride : int
      }
  | Broadcast of { size : int }
  | Group of t list
[@@deriving sexp_of, compare]

let rec validate = function
  | Axis { size; stride } ->
    if size < 1 || stride < 1
    then raise_s [%message "Linear.validate: malformed Axis" (size : int) (stride : int)]
  | Broadcast { size } ->
    if size < 1
    then raise_s [%message "Linear.validate: malformed Broadcast" (size : int)]
  | Group ts -> List.iter ts ~f:validate
;;

let rec shape : t -> Shape.t = function
  | Axis { size; _ } | Broadcast { size } -> Bound size
  | Group ts -> Product (List.map ts ~f:shape)
;;

let rec eval t (c : Coord.t) =
  match t, c with
  | Axis { stride; _ }, Idx i -> i * stride
  | Broadcast _, Idx _ -> 0
  | Group ts, Tuple cs ->
    (match List.fold2 ts cs ~init:0 ~f:(fun acc t c -> acc + eval t c) with
     | Ok n -> n
     | Unequal_lengths ->
       raise_s
         [%message
           "Linear.eval: wrong number of coordinates for group" (t : t) (c : Coord.t)])
  | (Axis _ | Broadcast _), Tuple _ | Group _, Idx _ ->
    raise_s
      [%message
        "Linear.eval: coordinate does not match layout structure" (t : t) (c : Coord.t)]
;;

let canonical (shape : Shape.t) : t =
  let rec go (shape : Shape.t) ~stride =
    match shape with
    | Bound n -> Axis { size = n; stride }, stride * n
    | Product ss ->
      let ts, stride =
        List.fold (List.rev ss) ~init:([], stride) ~f:(fun (acc, stride) s ->
          let t, stride = go s ~stride in
          t :: acc, stride)
      in
      Group ts, stride
  in
  fst (go shape ~stride:1)
;;

let rec max_offset = function
  | Axis { size; stride } -> (size - 1) * stride
  | Broadcast _ -> 0
  | Group ts -> List.sum (module Int) ts ~f:max_offset
;;

let cosize t = 1 + max_offset t

(* Multiply every stride; Broadcast contributes nothing either way. *)
let rec scale k = function
  | Axis { size; stride } -> Axis { size; stride = stride * k }
  | Broadcast _ as b -> b
  | Group ts -> Group (List.map ts ~f:(scale k))
;;

let rec broadcast_of_shape : Shape.t -> t = function
  | Bound n -> Broadcast { size = n }
  | Product ss -> Group (List.map ss ~f:broadcast_of_shape)
;;

let split ~by t =
  match t with
  | Axis { size; stride } when Shape.size by = size -> scale stride (canonical by)
  | Broadcast { size } when Shape.size by = size -> broadcast_of_shape by
  | Axis _ | Broadcast _ | Group _ ->
    raise_s
      [%message
        "Linear.split: expected a single axis whose size equals Shape.size by"
          (t : t)
          (by : Shape.t)]
;;

let var_name path =
  match path with
  | [] -> "c"
  | _ -> "c" ^ String.concat ~sep:"_" (List.map path ~f:Int.to_string)
;;

let divide ~by t =
  let rec go (by : Shape.t) t =
    match by, t with
    | Bound k, (Axis { size; _ } | Broadcast { size }) when size % k = 0 && k >= 1 ->
      (match split ~by:(Product [ Bound (size / k); Bound k ]) t with
       | Group [ rest; tile ] -> tile, rest
       | _ -> assert false)
    | Product bs, Group ts ->
      (match List.map2 bs ts ~f:go with
       | Ok pairs -> Group (List.map pairs ~f:fst), Group (List.map pairs ~f:snd)
       | Unequal_lengths ->
         raise_s
           [%message
             "Linear.divide: tiler does not match layout structure"
               (by : Shape.t)
               (t : t)])
    | Bound _, (Axis _ | Broadcast _ | Group _) | Product _, (Axis _ | Broadcast _) ->
      raise_s
        [%message
          "Linear.divide: tiler must be congruent with the shape and divide each axis"
            (by : Shape.t)
            (t : t)]
  in
  let tile, rest = go by t in
  Group [ tile; rest ]
;;

(* An arrangement is dense by definition: its strides say only in what
   ORDER the copies go (row-major grid, column-major grid, permuted),
   never where padding sits — padding lives in the strides of the tile
   itself, whose cosize then spaces the copies. A gapped [by] is a unit
   confusion, not an intent. *)
let check_arrangement ~op by =
  validate by;
  let n = Shape.size (shape by) in
  let image =
    List.map (Coord.enumerate (shape by)) ~f:(eval by) |> List.sort ~compare:Int.compare
  in
  if not (List.equal Int.equal image (List.init n ~f:Fn.id))
  then raise_s [%message (op ^ ": the arrangement [by] must be dense") (by : t)]
;;

let repeat ~by t =
  check_arrangement ~op:"Linear.repeat" by;
  Group [ scale (cosize t) by; t ]
;;

let broadcast ~by t = Group [ broadcast_of_shape by; t ]

let interleave ~by t =
  check_arrangement ~op:"Linear.interleave" by;
  Group [ by; scale (Shape.size (shape by)) t ]
;;

let is_dense t ~size =
  let broadcast_free = ref true in
  let total = ref 1 in
  let axes = ref [] in
  let rec go = function
    | Axis { size = 1; _ } | Broadcast { size = 1 } -> ()
    | Broadcast _ -> broadcast_free := false
    | Axis { size = n; stride = s } ->
      total := !total * n;
      axes := (n, s) :: !axes
    | Group ts -> List.iter ts ~f:go
  in
  go t;
  !broadcast_free
  && !total = size
  &&
  let sorted = List.sort !axes ~compare:(fun (_, a) (_, b) -> Int.compare a b) in
  let running =
    List.fold sorted ~init:(Some 1) ~f:(fun expect (n, s) ->
      match expect with
      | Some e when s = e -> Some (e * n)
      | Some _ | None -> None)
  in
  match running with
  | Some e -> e = size
  | None -> false
;;

(* Inverse of a DENSE layout, as a layout: index j |-> canonical index of
   the coordinate that maps to j. Density (Lemma: sorted strides are
   running products) makes the extraction exact: leaf i's index is
   (j / s_i) mod n_i, and it is re-encoded with leaf i's canonical
   weight in the original domain. The result's domain lists the digits
   from largest stride (outermost) to stride 1 (innermost). *)
let inverse t =
  let n = Shape.size (shape t) in
  if not (is_dense t ~size:n)
  then raise_s [%message "Linear.inverse: layout is not dense" (t : t)];
  (* leaves with their canonical weights in [t]'s own domain *)
  let rec leaves = function
    | Axis { size; stride } -> [ size, stride ]
    | Broadcast { size } -> [ size, 0 ]
    | Group ts -> List.concat_map ts ~f:leaves
  in
  let weighted, _ =
    List.fold_right (leaves t) ~init:([], 1) ~f:(fun (size, stride) (acc, w) ->
      (size, stride, w) :: acc, w * size)
  in
  let digits =
    List.filter weighted ~f:(fun (size, _, _) -> size > 1)
    |> List.sort ~compare:(fun (_, a, _) (_, b, _) -> Int.compare b a)
  in
  match digits with
  | [] -> Axis { size = 1; stride = 1 }
  | [ (size, _, w) ] -> Axis { size; stride = w }
  | ds -> Group (List.map ds ~f:(fun (size, _, w) -> Axis { size; stride = w }))
;;
