(* Executable oracle for the emitter. The test executables shadow
   [Layout], so every layout they build passes through here: both the
   pipeline and the emitted form must agree with [Layout.offset] at
   every coordinate, and a map that is affine over its coordinates must
   be DECIDED to that affine sum. Counters record what was emitted. *)
open! Base
open Layouts

let env_of_coord (c : Coord.t) : string -> int =
  let rec go path (c : Coord.t) acc =
    match c with
    | Idx i -> (Linear.var_name path, i) :: acc
    | Tuple cs -> List.foldi cs ~init:acc ~f:(fun j acc c -> go (path @ [ j ]) c acc)
  in
  let tbl = go [] c [] in
  fun name -> List.Assoc.find_exn tbl name ~equal:String.equal
;;

(* Classification of what the emitter produced. *)
let affine = ref 0 (* a single affine sum *)
let digits = ref 0 (* division/modulus of ONE variable each *)
let carry = ref 0 (* some division/modulus mixes variables *)

(* Is the map a single affine form over its coordinate variables? Fit
   the form from the origin and the unit coordinates, then check every
   point. This is the ground truth the simplifier is measured against. *)
let affine_fit t =
  let shape = Layout.shape t in
  let coords = Coord.enumerate shape in
  let origin = List.hd_exn coords in
  let k = Layout.offset t origin in
  let vars =
    let rec go path (s : Shape.t) acc =
      match s with
      | Bound n -> if n > 1 then (Linear.var_name path, n) :: acc else acc
      | Product ss -> List.foldi ss ~init:acc ~f:(fun j acc s -> go (path @ [ j ]) s acc)
    in
    List.rev (go [] shape [])
  in
  let unit name =
    List.find_exn coords ~f:(fun c ->
      let env = env_of_coord c in
      List.for_all vars ~f:(fun (v, _) -> env v = if String.equal v name then 1 else 0))
  in
  let strides = List.map vars ~f:(fun (v, _) -> v, Layout.offset t (unit v) - k) in
  let fits =
    List.for_all coords ~f:(fun c ->
      let env = env_of_coord c in
      Layout.offset t c = k + List.sum (module Int) strides ~f:(fun (v, s) -> s * env v))
  in
  if fits then Some (strides, k) else None

let emitted t =
  match Layout.strided_form t with
  | Some e -> e
  | None -> Layout.expr t
;;

let check_expr t =
  let pipeline = Layout.expr t in
  let e = emitted t in
  List.iter (Coord.enumerate (Layout.shape t)) ~f:(fun c ->
    let want = Layout.offset t c in
    List.iter [ "pipeline", pipeline; "emitted", e ] ~f:(fun (which, form) ->
      let got = Expr.eval form (env_of_coord c) in
      if got <> want
      then
        raise_s
          [%message
            "expression disagrees with evaluation"
              (which : string)
              (Expr.to_string form)
              (c : Coord.t)
              (got : int)
              (want : int)]));
  (* an affine map must be decided to its affine sum *)
  (match affine_fit t, Layout.strided_form t with
   | Some _, None -> raise_s [%message "affine map declared to have no strided form"]
   | Some _, Some form when not (Expr.is_affine form) ->
     raise_s [%message "affine map decided to a non-affine form" (Expr.to_string form)]
   | _ -> ());
  let rec single_var_digits : Expr.t -> bool = function
    | Const _ | Var _ -> true
    | Sum (ts, _) -> List.for_all ts ~f:(fun (_, t) -> single_var_digits t)
    | Div (x, _) | Mod (x, _) ->
      let rec vars : Expr.t -> string list = function
        | Const _ -> []
        | Var v -> [ v ]
        | Sum (ts, _) -> List.concat_map ts ~f:(fun (_, t) -> vars t)
        | Div (x, _) | Mod (x, _) -> vars x
        | Xor (a, b) -> vars a @ vars b
        | Let (_, e, b) -> vars e @ vars b
      in
      List.length (List.dedup_and_sort (vars x) ~compare:String.compare) <= 1
    | Xor _ | Let _ -> false
  in
  let bucket, label =
    if Expr.is_affine e
    then affine, "affine"
    else if single_var_digits e
    then digits, "digits"
    else carry, "carry"
  in
  Int.incr bucket;
  if (not (phys_equal bucket affine)) && Option.is_some (Sys.getenv "LAYOUT_SHOW_RESIDUAL")
  then Stdio.printf "%s: %s\n" label (Expr.to_string e)
;;

let report suite =
  Stdio.printf
    "%s: %d layouts oracle-checked; emitted %d affine, %d digits of one variable, %d as a pipeline\n"
    suite
    (!affine + !digits + !carry)
    !affine
    !digits
    !carry
;;

module Checked_layout = struct
  include Layout

  let checked t =
    check_expr t;
    t
  ;;

  let of_linear l = checked (of_linear l)
  let storage l = checked (storage l)
  let compose f g = checked (compose f g)
  let with_swizzle t sw = checked (with_swizzle t sw)
  let repeat ~by t = checked (repeat ~by t)
  let interleave ~by t = checked (interleave ~by t)
  let broadcast ~by t = checked (broadcast ~by t)
end
