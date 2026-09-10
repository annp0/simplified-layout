open! Base

type t =
  | Const of int
  | Var of string
  | Sum of (int * t) list * int
  | Div of t * int
  | Mod of t * int
  | Xor of t * t
  | Let of string * t * t
[@@deriving sexp_of, compare]

let var name = Var name

let fdiv a b =
  let q = a / b in
  if a % b <> 0 && Bool.( <> ) (a < 0) (b < 0) then q - 1 else q
;;

let fmod a b = a - (b * fdiv a b)

let affine = function
  | Const c -> [], c
  | Sum (ts, c) -> ts, c
  | e -> [ 1, e ], 0
;;

let atom_key = function
  | Var v -> 0, v
  | _ -> 1, ""
;;

let norm_terms ts =
  List.sort_and_group ts ~compare:(fun (_, a) (_, b) -> compare a b)
  |> List.filter_map ~f:(fun grp ->
    match grp with
    | [] -> None
    | (_, atom) :: _ ->
      let a = List.sum (module Int) grp ~f:fst in
      if a = 0 then None else Some (a, atom))
  |> List.sort ~compare:(fun (_, a) (_, b) ->
    match [%compare: int * string] (atom_key a) (atom_key b) with
    | 0 -> compare a b
    | c -> c)
;;

let mk_sum ts c =
  match norm_terms ts, c with
  | [], c -> Const c
  | [ (1, atom) ], 0 -> atom
  | ts, c -> Sum (ts, c)
;;

let add a b =
  let ta, ca = affine a
  and tb, cb = affine b in
  mk_sum (ta @ tb) (ca + cb)
;;

let scale k e =
  if k = 0
  then Const 0
  else (
    let ts, c = affine e in
    mk_sum (List.map ts ~f:(fun (a, t) -> k * a, t)) (k * c))
;;

let sum es = List.fold es ~init:(Const 0) ~f:add

let div e w =
  match e with
  | _ when w = 1 -> e
  | Const c -> Const (fdiv c w)
  | Div (x, w') -> Div (x, w * w')
  | _ -> Div (e, w)
;;

let modulo e r =
  match e with
  | _ when r = 1 -> Const 0
  | Const c -> Const (fmod c r)
  | Mod (x, r') when r' % r = 0 -> Mod (x, r)
  | _ -> Mod (e, r)
;;

let xor a b =
  match a, b with
  | Const x, Const y -> Const (x lxor y)
  | x, Const 0 | Const 0, x -> x
  | x, y -> Xor (x, y)
;;

(* a trivial binding is inlined rather than dropped *)
let rec replace e ~name ~by =
  match e with
  | Const _ -> e
  | Var v -> if String.equal v name then by else e
  | Sum (ts, c) -> mk_sum (List.map ts ~f:(fun (a, t) -> a, replace t ~name ~by)) c
  | Div (x, w) -> Div (replace x ~name ~by, w)
  | Mod (x, r) -> Mod (replace x ~name ~by, r)
  | Xor (a, b) -> Xor (replace a ~name ~by, replace b ~name ~by)
  | Let (x, e, body) ->
    if String.equal x name
    then Let (x, replace e ~name ~by, body)
    else Let (x, replace e ~name ~by, replace body ~name ~by)
;;

let bind name e body =
  match e with
  | Const _ | Var _ -> replace body ~name ~by:e
  | _ -> Let (name, e, body)
;;

let rec is_affine = function
  | Const _ | Var _ -> true
  | Sum (ts, _) -> List.for_all ts ~f:(fun (_, t) -> is_affine t)
  | Div _ | Mod _ | Xor _ | Let _ -> false
;;

let rec eval e env =
  match e with
  | Const c -> c
  | Var v -> env v
  | Sum (ts, c) -> List.fold ts ~init:c ~f:(fun acc (a, t) -> acc + (a * eval t env))
  | Div (e, w) -> fdiv (eval e env) w
  | Mod (e, r) -> fmod (eval e env) r
  | Xor (a, b) -> eval a env lxor eval b env
  | Let (x, e, body) ->
    let v = eval e env in
    eval body (fun n -> if String.equal n x then v else env n)
;;

let rec subst e env =
  match e with
  | Const _ -> e
  | Var v ->
    (match env v with
     | Some i -> Const i
     | None -> e)
  | Sum (ts, c) -> add (sum (List.map ts ~f:(fun (a, t) -> scale a (subst t env)))) (Const c)
  | Div (e, w) -> div (subst e env) w
  | Mod (e, r) -> modulo (subst e env) r
  | Xor (a, b) -> xor (subst a env) (subst b env)
  | Let (x, e, body) ->
    let e = subst e env in
    (match e with
     | Const v -> subst body (fun n -> if String.equal n x then Some v else env n)
     | e -> bind x e (subst body (fun n -> if String.equal n x then None else env n)))
;;

let rec to_string = function
  | Const c -> Int.to_string c
  | Var v -> v
  | Sum (ts, c) ->
    let terms =
      List.map ts ~f:(fun (a, t) ->
        if a = 1 then operand t else Printf.sprintf "%d*%s" a (operand t))
    in
    String.concat ~sep:" + " (terms @ if c <> 0 then [ Int.to_string c ] else [])
  | Div (e, w) -> Printf.sprintf "%s / %d" (operand e) w
  | Mod (e, r) -> Printf.sprintf "%s %% %d" (operand e) r
  | Xor (a, b) -> Printf.sprintf "%s ^ %s" (operand a) (operand b)
  | Let (x, e, body) -> Printf.sprintf "let %s = %s in %s" x (to_string e) (to_string body)

and operand e =
  match e with
  | Const _ | Var _ -> to_string e
  | _ -> Printf.sprintf "(%s)" (to_string e)
;;
