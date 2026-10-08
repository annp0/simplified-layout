(** * Lemma 1 for modes in any order

    [Dense.dense_iff_running] is stated for modes already sorted by
    stride, with every size at least two. The paper's Lemma 1 sorts the
    modes first and drops the modes of size [1] beforehand. This file
    closes both steps:

    - permuting the modes permutes the coordinates, so it changes
      neither the image nor injectivity ([dense_perm]);
    - a mode of size [1] has the single index [0] and contributes
      nothing ([dense_drop_ones]);
    - every list of modes has a sorted permutation ([sort_modes]).

    The result is [dense_iff_running_general]: a layout is a dense
    bijection onto [[0, N)] exactly when, after dropping its modes of
    size [1] and sorting the rest by stride, the strides are the running
    products of the sizes. *)

From Stdlib Require Import Arith Lia List Permutation.
From LayoutAlgebra Require Import Dense.
Import ListNotations.

(** ** Coordinate isomorphisms

    Two lists of modes whose coordinates correspond one to one, with
    the correspondence preserving the index function. *)

Definition CoordIso (L L' : modes) : Prop :=
  exists (f g : list nat -> list nat),
    (forall cs, coord_ok L cs ->
       coord_ok L' (f cs) /\ ev L' (f cs) = ev L cs /\ g (f cs) = cs)
    /\ (forall cs', coord_ok L' cs' ->
       coord_ok L (g cs') /\ ev L (g cs') = ev L' cs' /\ f (g cs') = cs').

Lemma coord_iso_sym (L L' : modes) : CoordIso L L' -> CoordIso L' L.
Proof. intros [f [g [A B]]]. exists g, f. split; assumption. Qed.

Lemma coord_iso_trans (L1 L2 L3 : modes) :
  CoordIso L1 L2 -> CoordIso L2 L3 -> CoordIso L1 L3.
Proof.
  intros [f1 [g1 [A1 B1]]] [f2 [g2 [A2 B2]]].
  exists (fun cs => f2 (f1 cs)), (fun cs => g1 (g2 cs)). split.
  - intros cs Hcs. destruct (A1 cs Hcs) as [H1 [E1 R1]].
    destruct (A2 _ H1) as [H2 [E2 R2]].
    split; [exact H2 |]. split; [lia |]. rewrite R2. exact R1.
  - intros cs Hcs. destruct (B2 cs Hcs) as [H1 [E1 R1]].
    destruct (B1 _ H1) as [H2 [E2 R2]].
    split; [exact H2 |]. split; [lia |]. rewrite R2. exact R1.
Qed.

(** A dense bijection stays one across a coordinate isomorphism of the
    same size. *)
Lemma dense_iso (w : nat) (L L' : modes) :
  CoordIso L L' -> msize L = msize L' -> Dense w L -> Dense w L'.
Proof.
  intros [f [g [A B]]] Hm [Himg [Hsurj Hinj]].
  split; [| split].
  - intros cs' Hcs'. destruct (B cs' Hcs') as [Hc [He _]].
    destruct (Himg _ Hc) as [k [Hk Hev]]. exists k. split; lia.
  - intros k Hk. destruct (Hsurj k ltac:(lia)) as [cs [Hcs Hev]].
    destruct (A cs Hcs) as [Hc' [He _]]. exists (f cs). split; [exact Hc' | lia].
  - intros c1 c2 H1 H2 Heq.
    destruct (B c1 H1) as [G1 [E1 R1]]. destruct (B c2 H2) as [G2 [E2 R2]].
    assert (Hg : g c1 = g c2) by (apply Hinj; [exact G1 | exact G2 | lia]).
    rewrite <- R1, <- R2, Hg. reflexivity.
Qed.

(** ** Permuting the modes *)

Lemma Forall_perm_transfer {A : Type} (P : A -> Prop) (l l' : list A) :
  Permutation l l' -> Forall P l -> Forall P l'.
Proof.
  intros Hp H. rewrite Forall_forall in *. intros x Hx.
  apply H. apply (Permutation_in x (Permutation_sym Hp) Hx).
Qed.

Lemma msize_perm (L L' : modes) : Permutation L L' -> msize L = msize L'.
Proof.
  induction 1 as [| x l l' Hp IH | x y l | l l' l'' H1 IH1 H2 IH2].
  - reflexivity.
  - destruct x as [n s]. simpl. rewrite IH. reflexivity.
  - destruct x as [n1 s1], y as [n2 s2]. simpl. ring.
  - rewrite IH1. exact IH2.
Qed.

Lemma perm_coord_iso (L L' : modes) : Permutation L L' -> CoordIso L L'.
Proof.
  induction 1 as [| x l l' Hp IH | x y l | l l' l'' H1 IH1 H2 IH2].
  - exists (fun cs => cs), (fun cs => cs).
    split; intros cs Hcs; (split; [exact Hcs | split; reflexivity]).
  - destruct IH as [f [g [A B]]]. destruct x as [n s].
    exists (fun cs => match cs with c :: r => c :: f r | [] => [] end),
           (fun cs => match cs with c :: r => c :: g r | [] => [] end).
    split.
    + intros cs Hcs. inversion Hcs as [| n0 s0 L0 c r Hc Hr]; subst.
      destruct (A r Hr) as [Hr' [E R]].
      split; [constructor; assumption |].
      split; [simpl; lia | rewrite R; reflexivity].
    + intros cs Hcs. inversion Hcs as [| n0 s0 L0 c r Hc Hr]; subst.
      destruct (B r Hr) as [Hr' [E R]].
      split; [constructor; assumption |].
      split; [simpl; lia | rewrite R; reflexivity].
  - destruct x as [n1 s1], y as [n2 s2].
    exists (fun cs => match cs with c1 :: c2 :: r => c2 :: c1 :: r | _ => cs end),
           (fun cs => match cs with c1 :: c2 :: r => c2 :: c1 :: r | _ => cs end).
    split.
    + intros cs Hcs. inversion Hcs as [| n0 s0 L0 c1 r1 Hc1 Hr1]; subst.
      inversion Hr1 as [| n3 s3 L3 c2 r Hc2 Hr]; subst.
      split; [constructor; [exact Hc2 | constructor; [exact Hc1 | exact Hr]] |].
      split; [simpl; lia | reflexivity].
    + intros cs Hcs. inversion Hcs as [| n0 s0 L0 c1 r1 Hc1 Hr1]; subst.
      inversion Hr1 as [| n3 s3 L3 c2 r Hc2 Hr]; subst.
      split; [constructor; [exact Hc2 | constructor; [exact Hc1 | exact Hr]] |].
      split; [simpl; lia | reflexivity].
  - exact (coord_iso_trans _ _ _ IH1 IH2).
Qed.

Theorem dense_perm (w : nat) (L L' : modes) :
  Permutation L L' -> Dense w L -> Dense w L'.
Proof.
  intros Hp. apply dense_iso; [apply perm_coord_iso, Hp | apply msize_perm, Hp].
Qed.

(** ** Sorting by stride *)

Fixpoint insert_mode (x : nat * nat) (L : modes) : modes :=
  match L with
  | [] => [x]
  | y :: r => if Nat.leb (snd x) (snd y) then x :: y :: r else y :: insert_mode x r
  end.

Fixpoint sort_modes (L : modes) : modes :=
  match L with
  | [] => []
  | x :: r => insert_mode x (sort_modes r)
  end.

Lemma insert_perm (x : nat * nat) (L : modes) :
  Permutation (x :: L) (insert_mode x L).
Proof.
  induction L as [| y r IH]; simpl; [reflexivity |].
  destruct (Nat.leb (snd x) (snd y)); [reflexivity |].
  transitivity (y :: x :: r); [apply perm_swap | apply perm_skip, IH].
Qed.

Lemma sort_perm (L : modes) : Permutation L (sort_modes L).
Proof.
  induction L as [| x r IH]; simpl; [reflexivity |].
  transitivity (x :: sort_modes r); [apply perm_skip, IH | apply insert_perm].
Qed.

Lemma insert_sorted (x : nat * nat) (L : modes) :
  sorted_strides L -> sorted_strides (insert_mode x L).
Proof.
  induction L as [| [n s] r IH]; intros Hs; destruct x as [nx sx].
  - simpl. split; [constructor | exact I].
  - simpl in Hs |- *. destruct Hs as [Hge Hsr].
    destruct (Nat.leb_spec sx s) as [Hle | Hgt]; simpl.
    + split; [| split; assumption].
      constructor; [simpl; exact Hle |].
      unfold strides_ge in *. eapply Forall_impl; [| exact Hge].
      intros m Hm. cbn beta in *. lia.
    + split; [| apply IH; exact Hsr].
      apply (Forall_perm_transfer _ ((nx, sx) :: r)); [apply insert_perm |].
      constructor; [simpl; lia | exact Hge].
Qed.

Lemma sort_sorted (L : modes) : sorted_strides (sort_modes L).
Proof.
  induction L as [| x r IH]; simpl; [exact I | apply insert_sorted, IH].
Qed.

(** Lemma 1 against ANY sorted arrangement of the modes. *)
Theorem dense_iff_running_perm (L L' : modes) :
  sizes_ge2 L -> strides_pos L -> Permutation L L' -> sorted_strides L' ->
  (Dense 1 L <-> running 1 L').
Proof.
  intros Hsz Hsp Hp Hsort.
  assert (Hsz' : sizes_ge2 L') by (eapply Forall_perm_transfer; eassumption).
  assert (Hsp' : strides_pos L') by (eapply Forall_perm_transfer; eassumption).
  rewrite <- (dense_iff_running L' Hsz' Hsp' Hsort).
  split; apply dense_perm; [exact Hp | apply Permutation_sym, Hp].
Qed.

Corollary dense_iff_running_sorted (L : modes) :
  sizes_ge2 L -> strides_pos L -> (Dense 1 L <-> running 1 (sort_modes L)).
Proof.
  intros Hsz Hsp.
  exact (dense_iff_running_perm L _ Hsz Hsp (sort_perm L) (sort_sorted L)).
Qed.

(** ** Dropping the modes of size 1 *)

(** Named, so that [simpl] leaves it folded under [filter]. *)
Definition big_mode (m : nat * nat) : bool := Nat.leb 2 (fst m).

Definition drop_ones (L : modes) : modes := filter big_mode L.

(** The coordinate without its size-1 entries, and back. *)
Fixpoint drop_c (L : modes) (cs : list nat) : list nat :=
  match L, cs with
  | (n, _) :: L', c :: cs' => if Nat.leb 2 n then c :: drop_c L' cs' else drop_c L' cs'
  | _, _ => []
  end.

Fixpoint fill_c (L : modes) (cs : list nat) : list nat :=
  match L with
  | [] => []
  | (n, _) :: L' =>
      if Nat.leb 2 n
      then match cs with
           | c :: cs' => c :: fill_c L' cs'
           | [] => 0 :: fill_c L' []
           end
      else 0 :: fill_c L' cs
  end.

Lemma drop_c_spec (L : modes) (cs : list nat) :
  sizes_pos L -> coord_ok L cs ->
  coord_ok (drop_ones L) (drop_c L cs)
  /\ ev (drop_ones L) (drop_c L cs) = ev L cs
  /\ fill_c L (drop_c L cs) = cs.
Proof.
  revert cs. induction L as [| [n s] L IH]; intros cs Hp Hcs.
  - inversion Hcs; subst. split; [constructor | split; reflexivity].
  - inversion Hcs as [| n0 s0 L0 c r Hc Hr]; subst.
    assert (Hn : (1 <= n)%nat) by (eapply sizes_pos_head; exact Hp).
    destruct (IH r (sizes_pos_tail _ _ _ Hp) Hr) as [H1 [E1 R1]].
    unfold drop_ones in *.
    destruct n as [| [| n']]; [lia | |]; simpl.
    + (* size 1: the index is 0 and is dropped *)
      assert (c = 0%nat) by lia. subst c.
      split; [exact H1 |]. split; [lia | rewrite R1; reflexivity].
    + split; [constructor; assumption |].
      split; [simpl; lia | rewrite R1; reflexivity].
Qed.

Lemma fill_c_spec (L : modes) (cs : list nat) :
  sizes_pos L -> coord_ok (drop_ones L) cs ->
  coord_ok L (fill_c L cs)
  /\ ev L (fill_c L cs) = ev (drop_ones L) cs
  /\ drop_c L (fill_c L cs) = cs.
Proof.
  revert cs. induction L as [| [n s] L IH]; intros cs Hp Hcs.
  - inversion Hcs; subst. split; [constructor | split; reflexivity].
  - assert (Hn : (1 <= n)%nat) by (eapply sizes_pos_head; exact Hp).
    assert (Hp' := sizes_pos_tail _ _ _ Hp).
    unfold drop_ones in *.
    destruct n as [| [| n']]; [lia | |]; simpl in Hcs |- *.
    + (* size 1: a 0 is put back *)
      destruct (IH cs Hp' Hcs) as [H1 [E1 R1]].
      split; [constructor; [lia | exact H1] |].
      split; [simpl; lia | exact R1].
    + inversion Hcs as [| n0 s0 L0 c r Hc Hr]; subst.
      destruct (IH r Hp' Hr) as [H1 [E1 R1]].
      split; [constructor; assumption |].
      split; [simpl; lia | simpl; rewrite R1; reflexivity].
Qed.

Lemma msize_drop_ones (L : modes) : sizes_pos L -> msize (drop_ones L) = msize L.
Proof.
  induction L as [| [n s] L IH]; intros Hp; [reflexivity |].
  assert (Hn : (1 <= n)%nat) by (eapply sizes_pos_head; exact Hp).
  specialize (IH (sizes_pos_tail _ _ _ Hp)).
  unfold drop_ones in *.
  destruct n as [| [| n']]; [lia | |]; simpl; rewrite IH; lia.
Qed.

Theorem dense_drop_ones (w : nat) (L : modes) :
  sizes_pos L -> (Dense w L <-> Dense w (drop_ones L)).
Proof.
  intros Hp.
  assert (Hiso : CoordIso L (drop_ones L)).
  { exists (drop_c L), (fill_c L). split.
    - intros cs Hcs. exact (drop_c_spec L cs Hp Hcs).
    - intros cs Hcs. exact (fill_c_spec L cs Hp Hcs). }
  split; apply dense_iso.
  - exact Hiso.
  - symmetry. apply msize_drop_ones, Hp.
  - apply coord_iso_sym, Hiso.
  - apply msize_drop_ones, Hp.
Qed.

(** ** Lemma 1, as the paper states it *)

Theorem dense_iff_running_general (L : modes) :
  sizes_pos L -> strides_pos L ->
  (Dense 1 L <-> running 1 (sort_modes (drop_ones L))).
Proof.
  intros Hp Hsp.
  rewrite (dense_drop_ones 1 L Hp).
  apply dense_iff_running_sorted.
  - unfold sizes_ge2, drop_ones. apply Forall_forall. intros m Hm.
    apply filter_In in Hm. destruct Hm as [_ Hm]. unfold big_mode in Hm.
    now apply Nat.leb_le.
  - unfold strides_pos, drop_ones in *. apply Forall_forall. intros m Hm.
    apply filter_In in Hm. destruct Hm as [Hm _].
    rewrite Forall_forall in Hsp. exact (Hsp m Hm).
Qed.
