(* The extracted scan against the implementation.

   coq/check.sh compares COUNTS computed inside Coq, which cannot reach
   n = 12: nat is unary and vm_compute over 177,147 maps is too slow.
   Extraction moves the verified scan into OCaml, so here the two run
   side by side over the whole enumeration the paper quotes, and are
   compared map by map rather than in aggregate.

   Three things are checked for every map:
     - the two agree on whether a strided form exists;
     - when one exists, both reconstruct g at every point;
     - the digits agree, up to radix-1 entries, which are vacuous
       ((v / w) mod 1 = 0) and which fit_axis short-circuits away for
       n = 1 while the extracted shape keeps one. *)
open! Base
open Layouts
module E = Layout_scan_extracted.Layout_scan

(* ---- Coq's nat and Z, to and from int ---- *)

let rec nat_of_int n = if n <= 0 then E.O else E.S (nat_of_int (n - 1))
let rec int_of_nat = function
  | E.O -> 0
  | E.S n -> 1 + int_of_nat n

let rec positive_of_int n =
  if n = 1 then E.XH
  else if n % 2 = 1 then E.XI (positive_of_int (n / 2))
  else E.XO (positive_of_int (n / 2))

let z_of_int n =
  if n = 0 then E.Z0 else if n > 0 then E.Zpos (positive_of_int n)
  else E.Zneg (positive_of_int (-n))

let rec int_of_positive = function
  | E.XH -> 1
  | E.XO p -> 2 * int_of_positive p
  | E.XI p -> (2 * int_of_positive p) + 1

let int_of_z = function
  | E.Z0 -> 0
  | E.Zpos p -> int_of_positive p
  | E.Zneg p -> -int_of_positive p

let rec list_of_coq = function
  | E.Nil -> []
  | E.Cons (x, xs) -> x :: list_of_coq xs

(* ---- the extracted scan, in fit_axis's shape: (radix, weight, stride) ---- *)

let extracted_fit g ~n =
  let gz v = z_of_int (g (int_of_nat v)) in
  match E.scan (nat_of_int n) gz with
  | E.None -> None
  | E.Some ws ->
    let sh = E.shape_of_chain (nat_of_int n) ws in
    Some
      (List.map (list_of_coq sh) ~f:(fun (E.Pair (E.Pair (w, m), s)) ->
         int_of_nat m, int_of_nat w, int_of_z s))
;;

(* radix-1 digits contribute nothing; drop them before comparing *)
let normalize ds = List.filter ds ~f:(fun (r, _, _) -> r > 1)

(* a digit list, evaluated: sum over digits of s * ((v / w) mod r) *)
let eval_digits ds v =
  List.sum (module Int) ds ~f:(fun (r, w, s) -> s * (v / w % r))
;;

let () =
  let checked = ref 0
  and accepted = ref 0 in
  List.iter [ 2, 5; 3, 5; 4, 5; 6, 3; 8, 3; 9, 3; 12, 3 ] ~f:(fun (n, k) ->
    let rec all t acc =
      if t = n
      then (
        let a = Array.of_list (List.rev acc) in
        let g v = a.(v) in
        Int.incr checked;
        let mine = Decide.fit_axis g ~n
        and theirs = extracted_fit g ~n in
        (* 1. the same verdict *)
        (match mine, theirs with
         | None, None -> ()
         | Some _, Some _ -> Int.incr accepted
         | _ ->
           raise_s
             [%message
               "extracted scan and fit_axis disagree on acceptance"
                 (n : int)
                 (Array.to_list a : int list)
                 (Option.is_some mine : bool)
                 (Option.is_some theirs : bool)]);
        (* 2. and, when accepted, the same function, digit for digit *)
        match mine, theirs with
        | Some dm, Some dt ->
          List.iter (List.init n ~f:Fn.id) ~f:(fun v ->
            if eval_digits dm v <> g v || eval_digits dt v <> g v
            then
              raise_s
                [%message
                  "a recovered form does not reproduce g"
                    (n : int)
                    (Array.to_list a : int list)
                    (v : int)]);
          let nm = normalize dm
          and nt = normalize dt in
          if not (List.equal (fun (a, b, c) (d, e, f) -> a = d && b = e && c = f) nm nt)
          then
            raise_s
              [%message
                "extracted scan and fit_axis return different digits"
                  (n : int)
                  (Array.to_list a : int list)
                  (nm : (int * int * int) list)
                  (nt : (int * int * int) list)]
        | _ -> ())
      else List.iter (List.init k ~f:Fn.id) ~f:(fun v -> all (t + 1) (v :: acc))
    in
    all 1 [ 0 ]);
  Stdio.printf
    "extracted scan vs fit_axis: %d maps, identical verdict and digits; %d strided\n"
    !checked
    !accepted;
  Test_util.emit "extracted.maps" !checked;
  Test_util.emit "extracted.strided" !accepted
;;
