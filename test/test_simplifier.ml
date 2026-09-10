(* How good is the emitter? Measured on random layouts rather than the
   hand-built ones the other suites carry.

   The generators produce the two shapes composition actually sees: a
   dense bijection on the left (a relabel/reshape of a random
   factorization) and a storage map on the right (random axis order,
   random padding, optionally swizzled).

   For every layout: the pipeline and the emitted form must agree with
   [Layout.offset] at every coordinate; a decided strided form must
   never disagree with the map; and a map that is affine over its
   coordinates must be decided to that affine sum, never missed. *)
open! Base
open Layouts

let rng = Random.State.make [| 7 |]
let pick l = List.nth_exn l (Random.State.int rng (List.length l))

let rec factor n =
  if n = 1
  then []
  else (
    let d = pick (List.filter (List.range 2 (n + 1)) ~f:(fun d -> n % d = 0)) in
    d :: factor (n / d))
;;

(* running-product strides over a random factorization, presented in a
   random domain order: dense by construction, arbitrary as a relabel *)
let random_dense n =
  let sizes = List.permute ~random_state:rng (factor n) in
  let _, strided =
    List.fold_right sizes ~init:(1, []) ~f:(fun size (w, acc) -> w * size, (size, w) :: acc)
  in
  Linear.Group
    (List.map
       (List.permute ~random_state:rng strided)
       ~f:(fun (size, stride) -> Linear.Axis { size; stride }))
;;

(* a storage map of the same size: random axis order, random padding
   between axes (so cosize exceeds size) *)
let random_storage n =
  let sizes = List.permute ~random_state:rng (factor n) in
  let _, strided =
    List.fold_right sizes ~init:(1, []) ~f:(fun size (w, acc) ->
      let pad = if Random.State.int rng 3 = 0 then 1 + Random.State.int rng 3 else 0 in
      (w * size) + pad, (size, w) :: acc)
  in
  Linear.Group
    (List.map
       (List.permute ~random_state:rng strided)
       ~f:(fun (size, stride) -> Linear.Axis { size; stride }))
;;

let env_of_coord (c : Coord.t) =
  let rec go path (c : Coord.t) acc =
    match c with
    | Idx i -> (Linear.var_name path, i) :: acc
    | Tuple cs -> List.foldi cs ~init:acc ~f:(fun j acc c -> go (path @ [ j ]) c acc)
  in
  let tbl = go [] c [] in
  fun name -> List.Assoc.find_exn tbl name ~equal:String.equal
;;

let is_affine_map t =
  let coords = Coord.enumerate (Layout.shape t) in
  let k = Layout.offset t (List.hd_exn coords) in
  let vars =
    let rec go path (s : Shape.t) acc =
      match s with
      | Bound n -> if n > 1 then (Linear.var_name path, n) :: acc else acc
      | Product ss -> List.foldi ss ~init:acc ~f:(fun j acc s -> go (path @ [ j ]) s acc)
    in
    List.rev (go [] (Layout.shape t) [])
  in
  let unit name =
    List.find_exn coords ~f:(fun c ->
      let env = env_of_coord c in
      List.for_all vars ~f:(fun (v, _) -> env v = if String.equal v name then 1 else 0))
  in
  let strides = List.map vars ~f:(fun (v, _) -> v, Layout.offset t (unit v) - k) in
  List.for_all coords ~f:(fun c ->
    let env = env_of_coord c in
    Layout.offset t c = k + List.sum (module Int) strides ~f:(fun (v, s) -> s * env v))
;;

let rec ops : Expr.t -> int = function
  | Const _ | Var _ -> 0
  | Sum (ts, _) -> List.sum (module Int) ts ~f:(fun (_, t) -> ops t)
  | Div (x, _) | Mod (x, _) -> 1 + ops x
  | Xor (a, b) -> 1 + ops a + ops b
  | Let (_, e, b) -> ops e + ops b
;;

(* the oracle every generated layout passes through *)
let checked t =
  let pipeline = Layout.expr t in
  let decided = Layout.strided_form t in
  let coords = Coord.enumerate (Layout.shape t) in
  List.iter coords ~f:(fun c ->
    let want = Layout.offset t c in
    if Expr.eval pipeline (env_of_coord c) <> want
    then raise_s [%message "pipeline disagrees" (Expr.to_string pipeline) (c : Coord.t)];
    match decided with
    | None -> ()
    | Some form ->
      if Expr.eval form (env_of_coord c) <> want
      then
        raise_s
          [%message "decided strided form is wrong" (Expr.to_string form) (c : Coord.t)]);
  (match is_affine_map t, decided with
   | true, None -> raise_s [%message "affine map declared to have no strided form"]
   | true, Some form when not (Expr.is_affine form) ->
     raise_s [%message "affine map decided to a non-affine form" (Expr.to_string form)]
   | _ -> ());
  pipeline, decided
;;

let sizes = [ 4; 6; 8; 12; 16; 18; 24; 32; 36; 48; 64 ]

(* ---- pairs: dense onto storage ---- *)

let () =
  let trials = 600 in
  let affine = ref 0
  and strided = ref 0
  and pipe_ops = ref 0
  and out_ops = ref 0 in
  for _ = 1 to trials do
    let n = pick sizes in
    let f : (Space.logical, Space.logical) Layout.t = Layout.of_linear (random_dense n) in
    let g : (Space.logical, Space.physical) Layout.t = Layout.storage (random_storage n) in
    let t = Layout.compose f g in
    let pipeline, decided = checked t in
    pipe_ops := !pipe_ops + ops pipeline;
    out_ops := !out_ops + (match decided with Some e -> ops e | None -> ops pipeline);
    if is_affine_map t then Int.incr affine;
    if Option.is_some decided then Int.incr strided
  done;
  Stdio.printf
    "random pairs: %d; affine maps %d (all decided); strided over a refinement %d; ops %d -> %d\n"
    trials
    !affine
    !strided
    !pipe_ops
    !out_ops
;;

(* ---- chains: two logical stages onto storage ---- *)

let () =
  let trials = 300 in
  let affine = ref 0
  and strided = ref 0 in
  for _ = 1 to trials do
    let n = pick sizes in
    let f1 : (Space.logical, Space.logical) Layout.t = Layout.of_linear (random_dense n) in
    let f2 : (Space.logical, Space.logical) Layout.t = Layout.of_linear (random_dense n) in
    let g : (Space.logical, Space.physical) Layout.t = Layout.storage (random_storage n) in
    let t = Layout.compose (Layout.compose f1 f2) g in
    let _, decided = checked t in
    if is_affine_map t then Int.incr affine;
    if Option.is_some decided then Int.incr strided
  done;
  Stdio.printf
    "random 3-stage chains: %d; affine maps %d (all decided); strided over a refinement %d\n"
    trials
    !affine
    !strided
;;

(* ---- swizzled storage ---- *)

let () =
  let trials = 300 in
  let strided = ref 0
  and strided_unswizzled = ref 0 in
  for _ = 1 to trials do
    let bits = 1 + Random.State.int rng 3 in
    let src = bits + Random.State.int rng 3 in
    let footprint = 1 lsl (src + bits) in
    let n = footprint * pick [ 1; 2; 4 ] in
    let f : (Space.logical, Space.logical) Layout.t = Layout.of_linear (random_dense n) in
    let plain : (Space.logical, Space.physical) Layout.t = Layout.storage (random_dense n) in
    let g = Layout.with_swizzle plain ({ bits; src; dst = 0 } : Swizzle.t) in
    let t = Layout.compose f g in
    let _ = checked t in
    let _ = checked (Layout.compose f plain) in
    if Option.is_some (Layout.strided_form t) then Int.incr strided;
    if Option.is_some (Layout.strided_form (Layout.compose f plain))
    then Int.incr strided_unswizzled
  done;
  Stdio.printf
    "random swizzled composites: %d; strided over a refinement %d (unswizzled: %d)\n"
    trials
    !strided
    !strided_unswizzled
;;

(* ---- the per-axis recognizer, against a brute-force oracle ----

   The recognizer scans first differences once. The oracle enumerates
   EVERY chain of divisors of [n], reads off the strides that chain
   forces, and checks them at every point. They must accept exactly the
   same functions, and the recognizer's chain must be the coarsest one
   the oracle accepts. Run over every function [g : [0,n) -> [0,k)] with
   [g 0 = 0], for small [n] and [k]. *)

(* Every refinement of [0,n) is a strictly increasing chain of divisors
   starting at 1 and ending below n, so that its radices are at least 2
   and multiply to n. *)
let divisor_chains n =
  let divisors m = List.filter (List.range 1 (m + 1)) ~f:(fun d -> m % d = 0) in
  let rec grow last =
    []
    :: List.concat_map
         (List.filter (divisors n) ~f:(fun d -> d > last && d % last = 0 && d < n))
         ~f:(fun d -> List.map (grow d) ~f:(fun rest -> d :: rest))
  in
  if n = 1 then [ [] ] else List.map (grow 1) ~f:(fun rest -> 1 :: rest)
;;

let oracle_accepts g ~n =
  List.exists (divisor_chains n) ~f:(fun ws ->
    let rec pairs = function
      | [] -> []
      | [ w ] -> [ w, n ]
      | w :: (next :: _ as rest) -> (w, next) :: pairs rest
    in
    let ds = List.map (pairs ws) ~f:(fun (w, next) -> w, next / w, g w) in
    List.for_all (List.init n ~f:Fn.id) ~f:(fun v ->
      g v = List.sum (module Int) ds ~f:(fun (w, r, s) -> s * (v / w % r))))
;;

let () =
  let checked = ref 0
  and accepted = ref 0 in
  List.iter [ 2; 3; 4; 6; 8; 9; 12 ] ~f:(fun n ->
    let k = if n <= 4 then 5 else 3 in
    let rec all_fns t acc =
      if t = n
      then [ List.rev acc ]
      else List.concat_map (List.init k ~f:Fn.id) ~f:(fun v -> all_fns (t + 1) (v :: acc))
    in
    List.iter (all_fns 1 [ 0 ]) ~f:(fun vs ->
      let a = Array.of_list vs in
      let g v = a.(v) in
      Int.incr checked;
      let mine = Decide.fit_axis g ~n in
      let theirs = oracle_accepts g ~n in
      if Bool.( <> ) (Option.is_some mine) theirs
      then
        raise_s
          [%message
            "recognizer and brute force disagree"
              (n : int)
              (vs : int list)
              (Option.is_some mine : bool)
              (theirs : bool)];
      match mine with
      | None -> ()
      | Some ds ->
        Int.incr accepted;
        (* reconstruction, and the chain is the coarsest accepted one *)
        List.iter (List.init n ~f:Fn.id) ~f:(fun v ->
          let got = List.sum (module Int) ds ~f:(fun (r, w, s) -> s * (v / w % r)) in
          if got <> g v
          then
            raise_s
              [%message "recognized form does not reproduce g" (n : int) (vs : int list)]);
        let boundaries = List.map ds ~f:(fun (_, w, _) -> w) in
        List.iter (divisor_chains n) ~f:(fun ws ->
          let rec pairs = function
            | [] -> []
            | [ w ] -> [ w, n ]
            | w :: (next :: _ as rest) -> (w, next) :: pairs rest
          in
          let cs = List.map (pairs ws) ~f:(fun (w, next) -> w, next / w, g w) in
          let works =
            List.for_all (List.init n ~f:Fn.id) ~f:(fun v ->
              g v = List.sum (module Int) cs ~f:(fun (w, r, s) -> s * (v / w % r)))
          in
          (* every accepted chain must contain the recognizer's
             boundaries: they are necessary, so its chain is coarsest *)
          if works
          then
            List.iter boundaries ~f:(fun b ->
              if not (List.mem ws b ~equal:( = ))
              then
                raise_s
                  [%message
                    "a coarser chain was accepted" (n : int) (vs : int list) (b : int)]))));
  Stdio.printf
    "per-axis recognizer: %d functions checked against brute force, %d strided\n"
    !checked
    !accepted
;;

(* weight 1 is a boundary of every refinement, whatever its stride: for
   g v = v / 2 on n = 4 the differences report only weight 2, but the
   refinement is (2, 2) with strides (0, 1), and dropping its first
   digit would leave radices whose product is not n *)
let () =
  (match Decide.fit_axis (fun v -> v / 2) ~n:4 with
   | Some [ (2, 1, 0); (2, 2, 1) ] -> ()
   | other ->
     raise_s
       [%message
         "weight 1 convention" (other : (int * int * int) list option)]);
  (* a constant map: the trivial refinement, one digit of radix n *)
  (match Decide.fit_axis (fun _ -> 0) ~n:6 with
   | Some [ (6, 1, 0) ] -> ()
   | other -> raise_s [%message "constant map" (other : (int * int * int) list option)]);
  (* a size-one axis has no digits *)
  match Decide.fit_axis (fun _ -> 0) ~n:1 with
  | Some [] -> ()
  | other -> raise_s [%message "unit axis" (other : (int * int * int) list option)]
;;

(* the other direction: build strided functions from a chain and random
   prices, and require the recognizer to accept and reproduce them *)
let () =
  let built = ref 0 in
  List.iter [ 2; 3; 4; 6; 8; 9; 12; 16; 18; 24; 30; 32; 36; 48; 64 ] ~f:(fun n ->
    List.iter (divisor_chains n) ~f:(fun ws ->
      for _ = 1 to 8 do
        let rec pairs = function
          | [] -> []
          | [ w ] -> [ w, n ]
          | w :: (next :: _ as rest) -> (w, next) :: pairs rest
        in
        let ds =
          List.map (pairs ws) ~f:(fun (w, next) ->
            w, next / w, Random.State.int rng 40 - 12)
        in
        let g v = List.sum (module Int) ds ~f:(fun (w, r, s) -> s * (v / w % r)) in
        Int.incr built;
        match Decide.fit_axis g ~n with
        | None -> raise_s [%message "built strided function was rejected" (n : int)]
        | Some got ->
          List.iter (List.init n ~f:Fn.id) ~f:(fun v ->
            let back = List.sum (module Int) got ~f:(fun (r, w, s) -> s * (v / w % r)) in
            if back <> g v
            then raise_s [%message "recovered form differs" (n : int) (v : int)]);
          (* coarsest: no boundary outside the chain it was built from *)
          List.iter got ~f:(fun (_, w, _) ->
            if not (List.mem ws w ~equal:( = ))
            then raise_s [%message "invented a boundary" (n : int) (w : int)])
      done));
  Stdio.printf "per-axis recognizer: %d constructed mixed-radix forms recovered\n" !built
;;

let () = Stdio.print_endline "emitter measurement passed"
