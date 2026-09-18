#!/bin/sh
# Compare the MECHANIZED scan with the IMPLEMENTED one.
#
# Recognize.scan (Coq) and Decide.fit_axis (OCaml) are two renderings of
# the same algorithm, so they must accept the same maps and recover the
# same shape. This runs both over every g : [0,n) -> [0,k) with g 0 = 0,
# for the parameters the paper's evaluation uses, and prints the counts
# side by side.
#
# The Coq side needs a switch with Coq; the OCaml side needs the project
# switch. Pass them as COQ_SWITCH and OCAML_SWITCH if they differ from
# the defaults.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"

COQ_SWITCH=${COQ_SWITCH:-vst-audit}
OCAML_SWITCH=${OCAML_SWITCH:-$root}

echo "== Coq (Recognize.scan) =="
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/counts.v" <<'EOF'
From Coq Require Import Arith List ZArith.
From LayoutAlgebra Require Import Check.
Import ListNotations.
Eval vm_compute in (count_total 2 5, count_accepted 2 5).
Eval vm_compute in (count_total 3 5, count_accepted 3 5).
Eval vm_compute in (count_total 4 5, count_accepted 4 5).
Eval vm_compute in (count_total 6 3, count_accepted 6 3).
Eval vm_compute in (count_total 8 3, count_accepted 8 3).
Eval vm_compute in (count_total 9 3, count_accepted 9 3).
Eval vm_compute in recovered 4 [0;1;1]%Z.
EOF
( eval "$(opam env --switch="$COQ_SWITCH" --set-switch)"
  make -C coq >/dev/null
  coqc -Q coq LayoutAlgebra -w -deprecated "$tmp/counts.v" )

echo
echo "== OCaml (Decide.fit_axis) =="
mkdir -p "$tmp/probe"
cat > "$tmp/probe/probe.ml" <<'EOF'
open! Base
open Layouts

let count n k =
  let total = ref 0 and accepted = ref 0 in
  let rec all t acc =
    if t = n
    then (
      let a = Array.of_list (List.rev acc) in
      Int.incr total;
      if Option.is_some (Decide.fit_axis (fun v -> a.(v)) ~n) then Int.incr accepted)
    else List.iter (List.init k ~f:Fn.id) ~f:(fun v -> all (t + 1) (v :: acc))
  in
  all 1 [ 0 ];
  !total, !accepted

let () =
  List.iter [ 2, 5; 3, 5; 4, 5; 6, 3; 8, 3; 9, 3 ] ~f:(fun (n, k) ->
    let t, a = count n k in
    Stdio.printf "n=%-3d k=%d  total=%-7d accepted=%d\n" n k t a);
  match Decide.fit_axis (fun v -> v / 2) ~n:4 with
  | None -> Stdio.print_endline "v/2 on n=4: rejected"
  | Some ds ->
    Stdio.printf
      "v/2 on n=4: %s\n"
      (String.concat ~sep:" " (List.map ds ~f:(fun (r, w, s) ->
         Printf.sprintf "(weight=%d,radix=%d,stride=%d)" w r s)))
EOF
cat > "$tmp/probe/dune" <<'EOF'
(executable (name probe) (libraries layouts base stdio) (preprocess (pps ppx_jane)))
EOF
cp -r "$tmp/probe" ./coq_check_probe
trap 'rm -rf "$tmp" ./coq_check_probe' EXIT
( eval "$(opam env --switch="$OCAML_SWITCH" --set-switch)"
  dune exec ./coq_check_probe/probe.exe )
