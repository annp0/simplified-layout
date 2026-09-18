(** * Floor arithmetic

    The two facts about integer division that the recognition theorem
    rests on:

    - a digit of a mixed-radix expansion is a difference of floor terms
      ([digit_as_floors]), which is what lets a layout's index function
      be rewritten as a weighted sum of [v / w];
    - the first difference of [v |-> v / w] is the indicator of the
      multiples of [w] ([floor_first_difference]), which is what lets
      the weights be read off the map one at a time.

    Indices are natural numbers and strides are integers, so the
    statements mix the two; everything is pushed through [Z.of_nat]. *)

From Coq Require Import Arith Lia ZArith.

Open Scope Z_scope.

(** ** Digits as differences of floors *)

(** [Nat.div_div] read in [Z]: dividing twice is dividing by the
    product. *)
Lemma nat_div_div_Z (v w m : nat) :
  (w <> 0)%nat -> (m <> 0)%nat ->
  Z.of_nat (v / w / m)%nat = Z.of_nat (v / (w * m))%nat.
Proof. intros Hw Hm. now rewrite Nat.Div0.div_div. Qed.

(** The paper's Lemma 3, first identity: for [w' = w * m],
    [(v / w) mod m = v / w - m * (v / w')]. No divisibility is needed
    beyond [w, m >= 1]: the second floor is taken at the product. *)
Lemma digit_as_floors (v w m : nat) :
  (w <> 0)%nat -> (m <> 0)%nat ->
  Z.of_nat ((v / w) mod m)%nat
  = Z.of_nat (v / w)%nat - Z.of_nat m * Z.of_nat (v / (w * m))%nat.
Proof.
  intros Hw Hm.
  rewrite <- nat_div_div_Z by assumption.
  rewrite Nat.Div0.mod_eq.
  rewrite Nat2Z.inj_sub by (apply Nat.Div0.mul_div_le).
  now rewrite Nat2Z.inj_mul.
Qed.

(** A digit vanishes once the index is below the weight times the
    radix: the expansion has run out. *)
Lemma digit_top (v w m : nat) :
  (w <> 0)%nat -> (m <> 0)%nat -> (v < w * m)%nat ->
  Z.of_nat ((v / w) mod m)%nat = Z.of_nat (v / w)%nat.
Proof.
  intros Hw Hm Hlt.
  rewrite digit_as_floors by assumption.
  rewrite (Nat.div_small v (w * m)) by exact Hlt.
  simpl. lia.
Qed.

(** ** First differences *)

(** The indicator of "[w] divides [t]", as an integer. *)
Definition divides_ind (w t : nat) : Z := if Nat.eqb (t mod w) 0 then 1 else 0.

Lemma divides_ind_true (w t : nat) : (t mod w = 0)%nat -> divides_ind w t = 1.
Proof. intros H. unfold divides_ind. now rewrite H. Qed.

Lemma divides_ind_false (w t : nat) : (t mod w <> 0)%nat -> divides_ind w t = 0.
Proof.
  intros H. unfold divides_ind.
  destruct (Nat.eqb_spec (t mod w) 0); [contradiction | reflexivity].
Qed.

(** The paper's Lemma 3, second ingredient:
    [floor(t/w) - floor((t-1)/w) = [w | t]] for [t >= 1]. This is the
    step that makes the scan possible --- a weight shows up in the first
    difference exactly at its own multiples. *)
Lemma floor_first_difference (w t : nat) :
  (w <> 0)%nat -> (1 <= t)%nat ->
  Z.of_nat (t / w)%nat - Z.of_nat ((t - 1) / w)%nat = divides_ind w t.
Proof.
  intros Hw Ht.
  assert (Hdm : t = (w * (t / w) + t mod w)%nat) by (apply Nat.Div0.div_mod).
  assert (Hub : (t mod w < w)%nat) by (apply Nat.mod_upper_bound; assumption).
  destruct (Nat.eq_dec (t mod w) 0) as [Hmod | Hmod].
  - (* w | t, so t = w * q with q >= 1, and (t-1)/w = q-1 *)
    rewrite divides_ind_true by assumption.
    assert (Hq1 : (1 <= t / w)%nat) by lia.
    (* [w * (t / w)] is an atom to lia, so the two nonlinear steps ---
       distributing over the subtraction, and the atom being at least
       [w] --- are supplied by hand *)
    assert (Hmul : (w * (t / w - 1) = w * (t / w) - w)%nat)
      by (rewrite Nat.mul_sub_distr_l; lia).
    assert (Hge : (w <= w * (t / w))%nat).
    { replace w with (w * 1)%nat at 1 by lia.
      apply Nat.mul_le_mono_l. lia. }
    assert (Hdiv : ((t - 1) / w = t / w - 1)%nat).
    { symmetry. apply (Nat.div_unique (t - 1) w (t / w - 1) (w - 1)); lia. }
    rewrite Hdiv. lia.
  - (* w does not divide t: the floor does not move *)
    rewrite divides_ind_false by assumption.
    assert (Hdiv : ((t - 1) / w = t / w)%nat).
    { symmetry. apply (Nat.div_unique (t - 1) w (t / w) (t mod w - 1)); lia. }
    rewrite Hdiv. lia.
Qed.

(** The floor terms all vanish at the origin, so every weighted sum of
    them does. *)
Lemma floor_zero (w : nat) : Z.of_nat (0 / w)%nat = 0.
Proof. destruct w; reflexivity. Qed.
