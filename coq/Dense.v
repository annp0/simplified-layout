(** * Lemma 1: dense bijections are exactly the running-product strides

    A layout with no replication is a list of modes [(n_i, s_i)]. Its
    index function sends a coordinate to [sum_i c_i s_i]. The lemma
    says: with the modes sorted by stride and every size at least two,
    the map is a bijection onto [[0, N)] iff [s_1 = 1] and
    [s_{j+1} = s_j n_j] --- the sorted strides are the running products
    of the sorted sizes.

    Everything here is stated for modes ALREADY SORTED by stride, which
    is where the mathematical content is; sorting is a permutation of
    the modes and permuting modes permutes the coordinates without
    changing the image or injectivity.

    The statement is scaled by a factor [w] ([Dense w L], [running w
    L]) rather than fixed at [1]. That is not generality for its own
    sake: it is what makes the induction go through, because peeling
    the first mode off a dense layout leaves a layout that is dense
    only after scaling by that mode's size. *)

From Coq Require Import Arith Lia ZArith List.
Import ListNotations.

(** ** Modes, coordinates, and the index function *)

(** One mode is a size and a stride. *)
Definition modes := list (nat * nat).

Fixpoint msize (L : modes) : nat :=
  match L with
  | [] => 1
  | (n, _) :: r => n * msize r
  end.

(** Every size is positive. A size of zero would make the coordinate
    set empty and the size zero, so every statement below would hold
    vacuously; requiring it keeps the lemma about real layouts. *)
Definition sizes_pos (L : modes) : Prop := Forall (fun m => (1 <= fst m)%nat) L.

Lemma sizes_pos_tail (n s : nat) (L : modes) :
  sizes_pos ((n, s) :: L) -> sizes_pos L.
Proof. intros H. now inversion H. Qed.

Lemma sizes_pos_head (n s : nat) (L : modes) :
  sizes_pos ((n, s) :: L) -> (1 <= n)%nat.
Proof. intros H. inversion H as [| ? ? Hh ?]. exact Hh. Qed.

Lemma msize_pos (L : modes) : sizes_pos L -> (1 <= msize L)%nat.
Proof.
  induction L as [| [n s] L IH]; intros Hp; simpl; [lia |].
  assert (Hn : (1 <= n)%nat) by (eapply sizes_pos_head; exact Hp).
  assert (Hm : (1 <= msize L)%nat) by (apply IH; eapply sizes_pos_tail; exact Hp).
  nia.
Qed.

(** A coordinate has one index per mode, each below its size. *)
Inductive coord_ok : modes -> list nat -> Prop :=
| coord_nil : coord_ok [] []
| coord_cons : forall n s L c cs,
    (c < n)%nat -> coord_ok L cs -> coord_ok ((n, s) :: L) (c :: cs).

Fixpoint ev (L : modes) (cs : list nat) : nat :=
  match L, cs with
  | (_, s) :: L', c :: cs' => c * s + ev L' cs'
  | _, _ => 0
  end.

(** ** The two sides of the lemma *)

(** The running-product condition: the first stride is [w] and each
    later one is the previous times the previous size. *)
Fixpoint running (w : nat) (L : modes) : Prop :=
  match L with
  | [] => True
  | (n, s) :: r => s = w /\ running (w * n) r
  end.

(** A bijection onto [w * [0, msize L)]. At [w = 1] this is exactly
    "dense bijection onto [[0, N)]". *)
Definition Dense (w : nat) (L : modes) : Prop :=
  (forall cs, coord_ok L cs -> exists k, (k < msize L)%nat /\ ev L cs = w * k)
  /\ (forall k, (k < msize L)%nat ->
        exists cs, coord_ok L cs /\ ev L cs = w * k)
  /\ (forall cs cs', coord_ok L cs -> coord_ok L cs' ->
        ev L cs = ev L cs' -> cs = cs').

(** ** The easy direction: running products give a bijection

    This is the direction a compiler relies on to ACCEPT a layout: it
    is the mixed-radix representation theorem. *)

Theorem running_dense (w : nat) (L : modes) :
  (1 <= w)%nat -> sizes_pos L -> running w L -> Dense w L.
Proof.
  revert w. induction L as [| [n s] L IH]; intros w Hw Hpos Hrun.
  - (* no modes: the one coordinate goes to 0 *)
    split; [| split].
    + intros cs Hcs. exists 0%nat. simpl. split; [lia |].
      inversion Hcs. lia.
    + intros k Hk. exists []. split; [constructor |].
      simpl in Hk. simpl. lia.
    + intros cs cs' Hcs Hcs' _. inversion Hcs; inversion Hcs'; reflexivity.
  - simpl in Hrun. destruct Hrun as [-> Hrun'].
    assert (Hn : (1 <= n)%nat) by (eapply sizes_pos_head; exact Hpos).
    assert (Hpos' : sizes_pos L) by (eapply sizes_pos_tail; exact Hpos).
    assert (Hms : (1 <= msize L)%nat) by (apply msize_pos; exact Hpos').
    assert (Hwn : (1 <= w * n)%nat) by nia.
    destruct (IH (w * n) Hwn Hpos' Hrun') as [Himg [Hsurj Hinj]].
    split; [| split].
    + (* image *)
      intros cs Hcs. inversion Hcs as [| n0 s0 L0 c cs0 Hc Hcs0]; subst.
      destruct (Himg cs0 Hcs0) as [k' [Hk' Hev']].
      exists (c + n * k')%nat. split.
      * simpl. assert (k' + 1 <= msize L)%nat by lia.
        apply Nat.lt_le_trans with (m := (n * (k' + 1))%nat); [lia |].
        apply Nat.mul_le_mono_l. lia.
      * simpl. rewrite Hev'. lia.
    + (* surjectivity: read the first index off by division *)
      intros k Hk. simpl in Hk.
      assert (Hdm : k = (n * (k / n) + k mod n)%nat) by (apply Nat.Div0.div_mod).
      assert (Hub : (k mod n < n)%nat) by (apply Nat.mod_upper_bound; lia).
      assert (Hq : (k / n < msize L)%nat)
        by (apply Nat.Div0.div_lt_upper_bound; lia).
      destruct (Hsurj (k / n)%nat Hq) as [cs' [Hcs' Hev']].
      exists ((k mod n) :: cs'). split; [constructor; assumption |].
      simpl. rewrite Hev'. lia.
    + (* injectivity *)
      intros cs cs' Hcs Hcs' Heq.
      inversion Hcs as [| n1 s1 L1 c cs1 Hc Hcs1]; subst.
      inversion Hcs' as [| n2 s2 L2 c' cs2 Hc' Hcs2]; subst.
      destruct (Himg cs1 Hcs1) as [k1 [Hk1 Hev1]].
      destruct (Himg cs2 Hcs2) as [k2 [Hk2 Hev2]].
      simpl in Heq. rewrite Hev1, Hev2 in Heq.
      (* w * (c + n k1) = w * (c' + n k2) with c, c' < n *)
      assert (Hsplit : (c + n * k1 = c' + n * k2)%nat) by nia.
      assert (Hc_eq : c = c') by
        (destruct (Nat.lt_trichotomy k1 k2) as [Hlt | [Heq' | Hgt]];
         [ assert (k1 + 1 <= k2)%nat by lia; nia
         | subst; lia
         | assert (k2 + 1 <= k1)%nat by lia; nia ]).
      subst c'.
      assert (Hk_eq : k1 = k2) by nia.
      f_equal. apply Hinj; [assumption | assumption |].
      rewrite Hev1, Hev2, Hk_eq. reflexivity.
Qed.
