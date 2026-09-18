(** * A differential check against the OCaml implementation

    The theorems above are about [Recognize.scan]. This file computes
    what that scan accepts, over every map [g : [0,n) -> [0,k)] with
    [g 0 = 0], so the numbers can be compared with what
    [Decide.fit_axis] accepts on the same enumeration --- the check
    that the MECHANIZED algorithm is the IMPLEMENTED one.

    Run [coq/check.sh] to compare the two. *)

From Coq Require Import Arith List ZArith.
From LayoutAlgebra Require Import Floors Chain Recognize Shape.
Import ListNotations.

(** Every list of [len] values drawn from [[0,k)]. *)
Fixpoint all_lists (k len : nat) : list (list Z) :=
  match len with
  | 0%nat => [[]]
  | S l => flat_map (fun tl => map (fun v => Z.of_nat v :: tl) (seq 0 k))
                    (all_lists k l)
  end.

(** A map from its table of values, with [g 0 = 0] forced. *)
Definition g_of (l : list Z) : nat -> Z := fun v => nth v (0 :: l) 0%Z.

Definition accepts (n : nat) (l : list Z) : bool :=
  match scan n (g_of l) with
  | Some _ => true
  | None => false
  end.

Definition count_accepted (n k : nat) : nat :=
  length (filter (accepts n) (all_lists k (n - 1))).

Definition count_total (n k : nat) : nat := length (all_lists k (n - 1)).

(** The shape recovered for one map, as (weight, radix, stride) per
    digit --- the same data [Decide.fit_axis] returns, in the same
    order. *)
Definition recovered (n : nat) (l : list Z) : option (list (nat * nat * Z)) :=
  match scan n (g_of l) with
  | Some ws => Some (shape_of_chain n ws)
  | None => None
  end.
