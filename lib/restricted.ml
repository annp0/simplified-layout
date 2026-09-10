open! Base

type ('dom, 'cod) t =
  { layout : ('dom, 'cod) Layout.t
  ; at : Coord.partial
  }

let rec check (at : Coord.partial) (s : Shape.t) =
  match at, s with
  | Free, _ -> ()
  | At i, Bound n ->
    if i < 0 || i >= n
    then raise_s [%message "Restricted.restrict: index out of bounds" (i : int) (n : int)]
  | Parts ps, Product ss ->
    (match List.iter2 ps ss ~f:check with
     | Ok () -> ()
     | Unequal_lengths ->
       raise_s
         [%message
           "Restricted.restrict: restriction does not match shape"
             (at : Coord.partial)
             (s : Shape.t)])
  | At _, Product _ | Parts _, Bound _ ->
    raise_s
      [%message
        "Restricted.restrict: restriction does not match shape"
          (at : Coord.partial)
          (s : Shape.t)]
;;

let restrict ~at layout =
  check at (Layout.shape layout);
  { layout; at }
;;

let layout t = t.layout
let restriction t = t.at

(* Union of restrictions. [b] is validated against the restricted shape
   before merging, so on a slot [a] already fixes, [b] is Free or At 0. *)
let rec merge (a : Coord.partial) (b : Coord.partial) : Coord.partial =
  match a, b with
  | a, Free -> a
  | Free, b -> b
  | At i, At 0 -> At i
  | Parts ps, Parts qs -> Parts (List.map2_exn ps qs ~f:merge)
  | At _, (At _ | Parts _) | Parts _, At _ -> assert false (* ruled out by [check] *)
;;

let rec restricted_shape (at : Coord.partial) (s : Shape.t) : Shape.t =
  match at, s with
  | Free, s -> s
  | At _, Bound _ -> Bound 1
  | Parts ps, Product ss -> Product (List.map2_exn ps ss ~f:restricted_shape)
  | At _, Product _ | Parts _, Bound _ -> assert false (* ruled out by [check] *)
;;

let shape t = restricted_shape t.at (Layout.shape t.layout)

let restrict_more ~at t =
  check at (shape t);
  { t with at = merge t.at at }
;;

let rec complete (at : Coord.partial) (c : Coord.t) : Coord.t =
  match at, c with
  | Free, c -> c
  | At i, Idx 0 -> Idx i
  | Parts ps, Tuple cs ->
    (match List.map2 ps cs ~f:complete with
     | Ok cs -> Tuple cs
     | Unequal_lengths ->
       raise_s
         [%message
           "Restricted.offset: coordinate does not match restriction"
             (at : Coord.partial)
             (c : Coord.t)])
  | At _, (Idx _ | Tuple _) | Parts _, Idx _ ->
    raise_s
      [%message
        "Restricted.offset: coordinate does not match restriction"
          (at : Coord.partial)
          (c : Coord.t)]
;;

let offset t c = Layout.offset t.layout (complete t.at c)

(* Slicing loses no completeness: the restricted map is decided in its
   own right, over the free coordinates, with the pinned contribution
   folded into the constant. *)
let strided_form t =
  Decide.strided_form ~shape:(shape t) ~offset:(offset t)
;;

let to_expr t =
  match strided_form t with
  | Some e -> Expr.to_string e
  | None ->
    let rec pins path (at : Coord.partial) =
      match at with
      | Free -> []
      | At i -> [ Linear.var_name path, i ]
      | Parts ps -> List.concat (List.mapi ps ~f:(fun j p -> pins (path @ [ j ]) p))
    in
    let env = pins [] t.at in
    Expr.to_string
      (Expr.subst (Layout.expr t.layout) (fun n ->
         List.Assoc.find env n ~equal:String.equal))
;;
