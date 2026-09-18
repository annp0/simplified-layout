(** * Chains, floor sums, and the bridge between the two forms

    A flat shape of size [n] with strides is, in the paper's notation,
    a chain of weights [1 = w_1 | w_2 | ... | w_k | n] together with a
    stride [s_j] per weight, and its index function is the DIGIT form

      digit:   sum_j s_j * ((v / w_j) mod m_j),   m_j = w_{j+1} / w_j.

    The recognition theorem works instead with the FLOOR form

      floor:   sum_j a_j * (v / w_j),

    because a floor term has a trivial first difference. This file
    defines both, and proves they are the same family of functions
    under the change of variables [a_j = s_j - m_{j-1} s_{j-1}] --- the
    paper's Lemma 3. It then characterizes the floor form by its first
    differences, which is what the scan reads. *)

From Coq Require Import Arith Lia ZArith List.
From LayoutAlgebra Require Import Floors.
Import ListNotations.

Open Scope Z_scope.

(** ** The floor form *)

(** [(w, a)] contributes [a * (v / w)]. *)
Definition fsum (ws : list (nat * Z)) (v : nat) : Z :=
  fold_right (fun p acc => snd p * Z.of_nat (v / fst p)%nat + acc) 0 ws.

(** Its first difference: [(w, a)] contributes [a] exactly at the
    multiples of [w]. *)
Definition dsum (ws : list (nat * Z)) (t : nat) : Z :=
  fold_right (fun p acc => snd p * divides_ind (fst p) t + acc) 0 ws.

Definition weights_pos (ws : list (nat * Z)) : Prop :=
  Forall (fun p => fst p <> 0%nat) ws.

Lemma fsum_zero (ws : list (nat * Z)) : fsum ws 0%nat = 0.
Proof.
  induction ws as [| p ws IH]; [reflexivity |].
  simpl. rewrite floor_zero, IH. lia.
Qed.

(** The first difference of the floor form is the indicator sum. *)
Lemma fsum_step (ws : list (nat * Z)) (t : nat) :
  weights_pos ws -> (1 <= t)%nat ->
  fsum ws t - fsum ws (t - 1)%nat = dsum ws t.
Proof.
  intros Hpos Ht.
  induction ws as [| p ws IH]; [simpl; lia |].
  inversion Hpos as [| ? ? Hp Hrest]; subst.
  simpl.
  rewrite <- (floor_first_difference (fst p) t Hp Ht).
  specialize (IH Hrest). lia.
Qed.

(** ** Representability, and its first-difference characterization *)

(** [g] is the floor form [ws] on the box [[0, n)]. *)
Definition Represents (n : nat) (g : nat -> Z) (ws : list (nat * Z)) : Prop :=
  forall v, (v < n)%nat -> g v = fsum ws v.

(** The paper's step from Lemma 3 to equation (eq:diff): on a map
    vanishing at the origin, being a floor form is a condition on first
    differences alone. *)
Lemma represents_iff (n : nat) (g : nat -> Z) (ws : list (nat * Z)) :
  g 0%nat = 0 -> weights_pos ws ->
  Represents n g ws
  <-> (forall t, (1 <= t)%nat -> (t < n)%nat -> g t - g (t - 1)%nat = dsum ws t).
Proof.
  intros Hg0 Hpos. split.
  - intros HR t Ht1 Htn.
    rewrite (HR t Htn), (HR (t - 1)%nat) by lia.
    now apply fsum_step.
  - intros Hdiff v. induction v as [| v IH]; intros Hv.
    + now rewrite Hg0, fsum_zero.
    + assert (Hv' : (v < n)%nat) by lia.
      specialize (IH Hv').
      specialize (Hdiff (S v) (le_n_S 0 v (Nat.le_0_l v)) Hv).
      rewrite <- (fsum_step ws (S v) Hpos) in Hdiff by lia.
      replace (S v - 1)%nat with v in * by lia.
      lia.
Qed.

(** ** The digit form, and the bridge *)

(** [(w, m, s)] contributes [s * ((v / w) mod m)]. *)
Definition dgsum (T : list (nat * nat * Z)) (v : nat) : Z :=
  fold_right (fun p acc => let '(w, m, s) := p in
                s * Z.of_nat ((v / w) mod m)%nat + acc) 0 T.

(** The size of the shape: the top weight times the top radix. Taking
    [nof [] = 0] makes the empty list vacuous under [v < nof T], which
    is what lets the bridge lemma be proved by a plain induction. *)
Fixpoint nof (T : list (nat * nat * Z)) : nat :=
  match T with
  | [] => 0%nat
  | (w, m, _) :: rest => match rest with
                         | [] => (w * m)%nat
                         | _ => nof rest
                         end
  end.

(** The head weight, with an irrelevant default. *)
Definition hw (T : list (nat * nat * Z)) : nat :=
  match T with
  | [] => 1%nat
  | (w, _, _) :: _ => w
  end.

(** Well-formed: positive weights and radices, and each weight the
    previous one times its radix --- the running-product condition that
    makes the weights a chain. *)
Fixpoint wf (T : list (nat * nat * Z)) : Prop :=
  match T with
  | [] => True
  | (w, m, _) :: rest =>
      (w <> 0)%nat /\ (m <> 0)%nat /\
      match rest with
      | [] => True
      | (w', _, _) :: _ => w' = (w * m)%nat /\ wf rest
      end
  end.

(** The change of variables [a_j = s_j - m_{j-1} s_{j-1}], threaded
    left to right as the incoming [m_{j-1} s_{j-1}]. *)
Fixpoint coeffs (prev : Z) (T : list (nat * nat * Z)) : list (nat * Z) :=
  match T with
  | [] => []
  | (w, m, s) :: rest => (w, s - prev) :: coeffs (Z.of_nat m * s) rest
  end.

Lemma coeffs_weights_pos (prev : Z) (T : list (nat * nat * Z)) :
  wf T -> weights_pos (coeffs prev T).
Proof.
  revert prev. induction T as [| p T IH]; intros prev Hwf.
  - constructor.
  - destruct p as [[w m] s]. simpl in Hwf.
    destruct Hwf as [Hw [Hm Hrest]].
    simpl. constructor; [exact Hw |].
    apply IH. destruct T as [| [[w' m'] s'] T']; [exact I | apply Hrest].
Qed.

(** Unfolding one entry, kept as lemmas so the bridge proof can rewrite
    without [simpl] unfolding the recursive calls it needs to keep. *)

Lemma dgsum_nil (v : nat) : dgsum [] v = 0.
Proof. reflexivity. Qed.

Lemma dgsum_cons (w m : nat) (s : Z) (T : list (nat * nat * Z)) (v : nat) :
  dgsum ((w, m, s) :: T) v = s * Z.of_nat ((v / w) mod m)%nat + dgsum T v.
Proof. reflexivity. Qed.

Lemma fsum_nil (v : nat) : fsum [] v = 0.
Proof. reflexivity. Qed.

Lemma fsum_cons (w : nat) (a : Z) (ws : list (nat * Z)) (v : nat) :
  fsum ((w, a) :: ws) v = a * Z.of_nat (v / w)%nat + fsum ws v.
Proof. reflexivity. Qed.

Lemma coeffs_nil (prev : Z) : coeffs prev [] = [].
Proof. reflexivity. Qed.

Lemma coeffs_cons (prev : Z) (w m : nat) (s : Z) (T : list (nat * nat * Z)) :
  coeffs prev ((w, m, s) :: T) = (w, s - prev) :: coeffs (Z.of_nat m * s) T.
Proof. reflexivity. Qed.

(** The paper's Lemma 3: the digit form and the floor form are the same
    function, under the change of variables. Stated with the incoming
    term [prev] explicit so that it can be proved by induction; the
    [-m_j s_j] that entry [j] contributes to the floor at weight
    [w_{j+1}] is exactly the [prev] the induction hands to entry
    [j+1], and the two cancel. *)
Lemma dgsum_fsum (T : list (nat * nat * Z)) (v : nat) (prev : Z) :
  wf T -> (v < nof T)%nat ->
  dgsum T v = fsum (coeffs prev T) v + prev * Z.of_nat (v / hw T)%nat.
Proof.
  revert prev. induction T as [| p T IH]; intros prev Hwf Hv.
  - simpl in Hv. lia.
  - destruct p as [[w m] s]. simpl in Hwf. destruct Hwf as [Hw [Hm Hrest]].
    destruct T as [| [[w' m'] s'] T'].
    + (* one entry: the top digit is the whole floor, since v < w * m *)
      assert (Hvwm : (v < w * m)%nat) by exact Hv.
      rewrite dgsum_cons, dgsum_nil, coeffs_cons, coeffs_nil, fsum_cons, fsum_nil.
      rewrite digit_top by assumption.
      unfold hw. ring.
    + (* at least two entries *)
      destruct Hrest as [Hw' HwfT].
      assert (Hv' : (v < nof ((w', m', s') :: T'))%nat) by exact Hv.
      rewrite dgsum_cons, coeffs_cons, fsum_cons.
      rewrite (digit_as_floors v w m Hw Hm).
      rewrite (IH (Z.of_nat m * s) HwfT Hv').
      unfold hw. rewrite Hw'. ring.
Qed.

Corollary dgsum_is_fsum (T : list (nat * nat * Z)) (v : nat) :
  wf T -> (v < nof T)%nat -> dgsum T v = fsum (coeffs 0 T) v.
Proof.
  intros Hwf Hv. rewrite (dgsum_fsum T v 0 Hwf Hv). ring.
Qed.
