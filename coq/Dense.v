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

(** ** The hard direction: a bijection forces running products

    This is the direction a compiler relies on to know the criterion
    does not REJECT a dense layout. The argument needs three
    hypotheses the paper also makes: the modes are sorted by stride,
    every size is at least two, and every stride is positive. *)

Definition strides_ge (s : nat) (L : modes) : Prop :=
  Forall (fun m => (s <= snd m)%nat) L.

(** Sorted by stride, phrased as "each stride bounds all later ones". *)
Fixpoint sorted_strides (L : modes) : Prop :=
  match L with
  | [] => True
  | (_, s) :: r => strides_ge s r /\ sorted_strides r
  end.

Definition sizes_ge2 (L : modes) : Prop := Forall (fun m => (2 <= fst m)%nat) L.
Definition strides_pos (L : modes) : Prop := Forall (fun m => (1 <= snd m)%nat) L.

Lemma sizes_ge2_pos (L : modes) : sizes_ge2 L -> sizes_pos L.
Proof.
  induction L as [| [n s] L IH]; intros H; [constructor |].
  inversion H as [| ? ? Hh Ht]; subst.
  constructor; [simpl in *; lia | now apply IH].
Qed.

(** The all-zero coordinate. *)
Fixpoint zeros (L : modes) : list nat :=
  match L with
  | [] => []
  | _ :: r => 0%nat :: zeros r
  end.

Lemma coord_ok_zeros (L : modes) : sizes_pos L -> coord_ok L (zeros L).
Proof.
  induction L as [| [n s] L IH]; intros Hp; [constructor |].
  simpl. constructor.
  - pose proof (sizes_pos_head n s L Hp). lia.
  - apply IH. eapply sizes_pos_tail; exact Hp.
Qed.

Lemma ev_zeros (L : modes) : ev L (zeros L) = 0%nat.
Proof.
  induction L as [| [n s] L IH]; [reflexivity |].
  simpl. rewrite IH. lia.
Qed.

(** A nonzero value is at least the smallest stride: this is where
    sortedness is used. *)
Lemma ev_pos_ge (s : nat) (L : modes) (cs : list nat) :
  strides_ge s L -> coord_ok L cs -> (0 < ev L cs)%nat -> (s <= ev L cs)%nat.
Proof.
  intros Hge Hcs. revert Hge.
  induction Hcs as [| n s0 L0 c cs0 Hc Hcs0 IH]; intros Hge Hpos.
  - simpl in Hpos. lia.
  - inversion Hge as [| ? ? Hh Ht]; subst. simpl in Hh, Hpos |- *.
    destruct (Nat.eq_dec c 0) as [-> | Hcne].
    + simpl in Hpos |- *. specialize (IH Ht). lia.
    + assert (1 <= c)%nat by lia. nia.
Qed.

(** *** The alignment lemma

    Disjoint blocks of [n] consecutive positions that cover [[0, M)]
    are the ALIGNED ones. This replaces the paper's counting argument
    ("those modes produce at most [N_{j-1}] values"): covering comes
    from surjectivity and disjointness from injectivity, so no
    cardinality reasoning is needed. *)
Lemma alignment (n M : nat) (Kp : nat -> Prop) :
  (1 <= n)%nat ->
  (forall k, Kp k -> (k + n <= M)%nat) ->
  (forall x, (x < M)%nat ->
     exists k c, Kp k /\ (c < n)%nat /\ x = (k + c)%nat) ->
  (forall k k' c c', Kp k -> Kp k' -> (c < n)%nat -> (c' < n)%nat ->
     (k + c = k' + c')%nat -> k = k') ->
  forall k, Kp k -> Nat.divide n k.
Proof.
  intros Hn Hbound Hcover Hdisj k.
  induction k as [k IH] using (well_founded_induction lt_wf).
  intros Hk.
  destruct (Nat.eq_dec (k mod n) 0) as [Hr | Hr].
  - apply Nat.Lcm0.mod_divide; exact Hr.
  - exfalso.
    assert (Hdm : k = (n * (k / n) + k mod n)%nat) by (apply Nat.Div0.div_mod).
    assert (Hub : (k mod n < n)%nat) by (apply Nat.mod_upper_bound; lia).
    set (r := (k mod n)%nat) in *.
    assert (Hr1 : (1 <= r)%nat) by lia.
    assert (HkM : (k < M)%nat) by (pose proof (Hbound k Hk); lia).
    (* the aligned position just below k is covered by some block *)
    destruct (Hcover (k - r)%nat) as [k' [c' [Hk' [Hc' Heq]]]]; [lia |].
    assert (Hk'le : (k' <= k - r)%nat) by lia.
    assert (Hk'lt : (k' < k)%nat) by lia.
    (* by induction that block is aligned, and so is k - r, so c' = 0 *)
    assert (Hdk' : Nat.divide n k') by (apply IH; assumption).
    assert (Hdkr : Nat.divide n (k - r)%nat).
    { exists (k / n)%nat. lia. }
    assert (Hdc' : Nat.divide n c').
    { destruct Hdk' as [q Hq]. destruct Hdkr as [q' Hq'].
      exists (q' - q)%nat.
      rewrite Nat.mul_sub_distr_r. lia. }
    assert (Hc'0 : c' = 0%nat).
    { destruct Hdc' as [q Hq]. destruct q; [lia |]. nia. }
    subst c'. rewrite Nat.add_0_r in Heq. subst k'.
    (* k and k - r start blocks that both contain k: they must be equal *)
    assert (Hcontra : k = (k - r)%nat).
    { apply (Hdisj k (k - r)%nat 0%nat r Hk Hk'); [lia | lia | lia]. }
    lia.
Qed.

(** The converse of [running_dense]. *)
Theorem dense_running (w : nat) (L : modes) :
  (1 <= w)%nat -> sizes_ge2 L -> strides_pos L -> sorted_strides L ->
  Dense w L -> running w L.
Proof.
  revert w. induction L as [| [n s] L' IH]; intros w Hw Hsz Hsp Hsort HD;
    [exact I |].
  destruct HD as [Himg [Hsurj Hinj]].
  assert (Hn2 : (2 <= n)%nat) by (inversion Hsz as [| ? ? Hh ?]; exact Hh).
  assert (Hs1 : (1 <= s)%nat) by (inversion Hsp as [| ? ? Hh ?]; exact Hh).
  assert (Hsz' : sizes_ge2 L') by (inversion Hsz; assumption).
  assert (Hsp' : strides_pos L') by (inversion Hsp; assumption).
  destruct Hsort as [Hge' Hsort'].
  assert (Hpos' : sizes_pos L') by (apply sizes_ge2_pos; exact Hsz').
  assert (Hpos : sizes_pos ((n, s) :: L'))
    by (constructor; [simpl; lia | exact Hpos']).
  assert (Hm' : (1 <= msize L')%nat) by (apply msize_pos; exact Hpos').
  assert (HmL : (2 <= msize ((n, s) :: L'))%nat) by (simpl; nia).

  (* ---- step 1: the first stride is w ---- *)
  assert (Hsw : s = w).
  { (* s <= w: w is attained, and every nonzero value is at least s *)
    destruct (Hsurj 1%nat) as [cs [Hcs Hev]]; [lia |].
    assert (Hle : (s <= ev ((n, s) :: L') cs)%nat).
    { apply ev_pos_ge; [constructor; [simpl; lia | exact Hge'] | exact Hcs | lia]. }
    rewrite Hev in Hle.
    (* w <= s: s is itself an image value, so a positive multiple of w *)
    assert (Hev_e1 : ev ((n, s) :: L') (1%nat :: zeros L') = s).
    { simpl. rewrite ev_zeros. lia. }
    destruct (Himg (1%nat :: zeros L')) as [k [Hk Hkev]].
    { constructor; [lia | apply coord_ok_zeros; exact Hpos']. }
    rewrite Hev_e1 in Hkev.
    rewrite Nat.mul_1_r in Hle.
    (* s = w * k with s >= 1 forces k >= 1, hence s >= w *)
    assert (Hk1 : (1 <= k)%nat) by (destruct k; lia).
    nia. }
  subst s.

  (* ---- step 2: the tail's values, as multiples of w ---- *)
  set (Kp := fun k => exists cs', coord_ok L' cs' /\ ev L' cs' = (w * k)%nat).
  assert (Hbound : forall k, Kp k -> (k + n <= n * msize L')%nat).
  { intros k [cs' [Hcs' Hev']].
    destruct (Himg ((n - 1)%nat :: cs')) as [k2 [Hk2 Hkev2]];
      [constructor; [lia | exact Hcs'] |].
    simpl in Hkev2. rewrite Hev' in Hkev2. simpl in Hk2. nia. }
  assert (Hcover : forall x, (x < n * msize L')%nat ->
            exists k c, Kp k /\ (c < n)%nat /\ x = (k + c)%nat).
  { intros x Hx.
    destruct (Hsurj x) as [cs [Hcs Hev]]; [simpl; exact Hx |].
    inversion Hcs as [| n0 s0 L0 c cs' Hc Hcs']; subst.
    simpl in Hev.
    assert (Hcx : (c <= x)%nat) by nia.
    exists (x - c)%nat, c. split; [| split; [exact Hc | lia]].
    exists cs'. split; [exact Hcs' | nia]. }
  assert (Hdisj : forall k k' c c', Kp k -> Kp k' -> (c < n)%nat -> (c' < n)%nat ->
            (k + c = k' + c')%nat -> k = k').
  { intros k k' c c' [cs1 [Hcs1 Hev1]] [cs2 [Hcs2 Hev2]] Hc Hc' Hsum.
    assert (Heq : ev ((n, w) :: L') (c :: cs1) = ev ((n, w) :: L') (c' :: cs2)).
    { simpl. rewrite Hev1, Hev2. nia. }
    assert (Hcc : (c :: cs1) = (c' :: cs2))
      by (apply Hinj; [constructor; assumption | constructor; assumption | exact Heq]).
    injection Hcc as -> ->. nia. }
  assert (Halign : forall k, Kp k -> Nat.divide n k)
    by (apply (alignment n (n * msize L')%nat Kp); [lia | exact Hbound
        | exact Hcover | exact Hdisj]).

  (* every tail value is w times an element of Kp *)
  assert (Htail : forall cs', coord_ok L' cs' ->
            exists k, Kp k /\ ev L' cs' = (w * k)%nat).
  { intros cs' Hcs'.
    destruct (Himg (0%nat :: cs')) as [k [Hk Hkev]];
      [constructor; [lia | exact Hcs'] |].
    simpl in Hkev.
    exists k. split; [exists cs'; split; [exact Hcs' | lia] | lia]. }

  (* ---- step 3: the tail is dense, scaled by w * n ---- *)
  assert (HD' : Dense (w * n) L').
  { split; [| split].
    - (* image: alignment turns the factor w into w * n *)
      intros cs' Hcs'.
      destruct (Htail cs' Hcs') as [k [Hk Hev']].
      destruct (Halign _ Hk) as [q Hq].
      exists q. split.
      + pose proof (Hbound _ Hk) as Hb. nia.
      + rewrite Hev', Hq. ring.
    - (* surjectivity: the aligned position n * q is covered, and
         alignment forces the offset within its block to be zero *)
      intros q Hq.
      destruct (Hcover (n * q)%nat) as [k [c [Hk [Hc Heq]]]]; [nia |].
      destruct (Halign _ Hk) as [q' Hq'].
      assert (Hc0 : c = 0%nat).
      { assert (Hdc : Nat.divide n c).
        { exists (q - q')%nat. rewrite Nat.mul_sub_distr_r. nia. }
        destruct Hdc as [z Hz]. destruct z; [lia | nia]. }
      subst c. rewrite Nat.add_0_r in Heq.
      destruct Hk as [cs' [Hcs' Hev']].
      exists cs'. split; [exact Hcs' |].
      rewrite Hev', <- Heq. ring.
    - (* injectivity: restrict the whole layout's to the first index 0 *)
      intros cs1 cs2 Hcs1 Hcs2 Heq.
      assert (Hcc : (0%nat :: cs1) = (0%nat :: cs2)).
      { apply Hinj; [constructor; [lia | exact Hcs1]
                    | constructor; [lia | exact Hcs2] |].
        simpl. lia. }
      now injection Hcc as ->. }

  (* ---- step 4: recurse ---- *)
  split; [reflexivity |].
  apply IH; [nia | exact Hsz' | exact Hsp' | exact Hsort' | exact HD'].
Qed.

(** Lemma 1 of the paper, both directions, at [w = 1]: a layout whose
    modes are sorted by stride, with every size at least two and every
    stride positive, is a dense bijection onto [[0, N)] exactly when
    its sorted strides are the running products of its sorted sizes. *)
Theorem dense_iff_running (L : modes) :
  sizes_ge2 L -> strides_pos L -> sorted_strides L ->
  (Dense 1 L <-> running 1 L).
Proof.
  intros Hsz Hsp Hsort. split.
  - intros HD. apply (dense_running 1 L); [lia | assumption .. ].
  - intros Hr. apply (running_dense 1 L);
      [lia | apply sizes_ge2_pos; exact Hsz | exact Hr].
Qed.
