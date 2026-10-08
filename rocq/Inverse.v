(** * inverse

    Section 3: for a dense bijection [L] with modes [(n_i, d_i)], give
    mode [i] the canonical weight [w_i = prod_{j>i} n_j] and list the
    modes in decreasing order of stride; [inverse L] has those sizes and
    those weights. Read as maps on [[0, N)], each unflattening the
    integer it is given into its own shape, [L] and [inverse L] are
    mutually inverse ([inverse_left], [inverse_right]), and [inverse L]
    is again a dense bijection ([inverse_dense]).

    The argument: by Lemma 1, [L]'s modes listed by decreasing stride
    are the canonical layout of their own sizes, so unflattening [L x]
    into that shape gives back the coordinate of [x], reordered; and
    [inverse L] weighs that coordinate with [L]'s canonical weights,
    which is flattening it into [L]'s shape. As in Lemma 1, every size
    is at least two: a mode of size 1 is dropped beforehand. *)

From Stdlib Require Import Arith Lia List Permutation.
From LayoutAlgebra Require Import Dense DenseSort Ops.
Import ListNotations.

(** ** Unflattening, the inverse of [Ops.flat] *)

Fixpoint unflatten (S : list nat) (x : nat) : list nat :=
  match S with
  | [] => []
  | n :: S' => x / sprod S' :: unflatten S' (x mod sprod S')
  end.

Lemma sprod_pos (S : list nat) : Forall (fun n => 1 <= n) S -> 1 <= sprod S.
Proof.
  induction S as [| n S IH]; intros H; simpl; [lia |].
  inversion H; subst. specialize (IH ltac:(assumption)). nia.
Qed.

Lemma unflatten_spec (S : list nat) (x : nat) :
  Forall (fun n => 1 <= n) S -> x < sprod S ->
  coord_ok (canonical S) (unflatten S x) /\ flat S (unflatten S x) = x.
Proof.
  revert x. induction S as [| n S IH]; intros x Hp Hx.
  - simpl in Hx. split; [constructor | simpl; lia].
  - inversion Hp as [| ? ? Hn Hp']; subst.
    assert (HP : 1 <= sprod S) by (apply sprod_pos, Hp').
    simpl in Hx.
    destruct (IH (x mod sprod S) Hp' ltac:(apply Nat.mod_upper_bound; lia)) as [Hc Hf].
    split.
    + simpl. constructor; [apply Nat.Div0.div_lt_upper_bound; nia | exact Hc].
    + simpl. rewrite Hf. rewrite (Nat.div_mod_eq x (sprod S)) at 3. ring.
Qed.

Lemma map_fst_canonical (S : list nat) : map fst (canonical S) = S.
Proof. induction S as [| n S IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma msize_sprod (L : modes) : msize L = sprod (map fst L).
Proof. induction L as [| [n s] L IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** Validity of a coordinate depends on the sizes alone. *)
Lemma coord_ok_sizes (L L' : modes) (cs : list nat) :
  map fst L = map fst L' -> coord_ok L cs -> coord_ok L' cs.
Proof.
  revert L' cs. induction L as [| [n s] L IH]; intros L' cs Hm Hc;
    destruct L' as [| [n' s'] L']; try discriminate.
  - exact Hc.
  - simpl in Hm. injection Hm as -> Hm.
    inversion Hc as [| n0 s0 L0 c r Hcn Hr]; subst.
    constructor; [exact Hcn | apply (IH L'); assumption].
Qed.

Lemma flat_inj (S c c' : list nat) :
  Forall (fun n => 1 <= n) S ->
  coord_ok (canonical S) c -> coord_ok (canonical S) c' -> flat S c = flat S c' -> c = c'.
Proof.
  intros Hp Hc Hc' E. destruct (canonical_dense S Hp) as [_ [_ Hinj]].
  apply Hinj; [exact Hc | exact Hc' | rewrite !ev_canonical; lia].
Qed.

Lemma flat_lt (S c : list nat) :
  Forall (fun n => 1 <= n) S -> coord_ok (canonical S) c -> flat S c < sprod S.
Proof.
  intros Hp Hc. destruct (canonical_dense S Hp) as [Himg _].
  destruct (Himg c Hc) as [k [Hk E]].
  rewrite ev_canonical in E. rewrite msize_canonical in Hk. lia.
Qed.

Lemma unflatten_flat (S c : list nat) :
  Forall (fun n => 1 <= n) S -> coord_ok (canonical S) c -> unflatten S (flat S c) = c.
Proof.
  intros Hp Hc.
  destruct (unflatten_spec S (flat S c) Hp (flat_lt S c Hp Hc)) as [Hc' Hf].
  apply (flat_inj S); assumption.
Qed.

(** ** Sorting by a key, in decreasing order *)

Section SortDesc.
  Context {A : Type} (key : A -> nat).

  Fixpoint ins_desc (x : A) (l : list A) : list A :=
    match l with
    | [] => [x]
    | y :: r => if Nat.leb (key y) (key x) then x :: y :: r else y :: ins_desc x r
    end.

  Fixpoint sort_desc (l : list A) : list A :=
    match l with [] => [] | x :: r => ins_desc x (sort_desc r) end.

  Fixpoint sorted_desc (l : list A) : Prop :=
    match l with
    | [] => True
    | x :: r => Forall (fun y => key y <= key x) r /\ sorted_desc r
    end.

  Lemma ins_desc_perm (x : A) (l : list A) : Permutation (x :: l) (ins_desc x l).
  Proof.
    induction l as [| y r IH]; simpl; [reflexivity |].
    destruct (Nat.leb (key y) (key x)); [reflexivity |].
    transitivity (y :: x :: r); [apply perm_swap | apply perm_skip, IH].
  Qed.

  Lemma sort_desc_perm (l : list A) : Permutation l (sort_desc l).
  Proof.
    induction l as [| x r IH]; simpl; [reflexivity |].
    transitivity (x :: sort_desc r); [apply perm_skip, IH | apply ins_desc_perm].
  Qed.

  Lemma ins_desc_sorted (x : A) (l : list A) :
    sorted_desc l -> sorted_desc (ins_desc x l).
  Proof.
    induction l as [| y r IH]; intros Hs; simpl.
    - split; [constructor | exact I].
    - destruct Hs as [Hge Hsr].
      destruct (Nat.leb_spec (key y) (key x)) as [Hle | Hgt]; simpl.
      + split; [| split; assumption].
        constructor; [exact Hle |].
        eapply Forall_impl; [| exact Hge]. intros z Hz. cbn beta in *. lia.
      + split; [| apply IH; exact Hsr].
        apply (Forall_perm_transfer _ (x :: r)); [apply ins_desc_perm |].
        constructor; [lia | exact Hge].
  Qed.

  Lemma sort_desc_sorted (l : list A) : sorted_desc (sort_desc l).
  Proof.
    induction l as [| x r IH]; simpl; [exact I | apply ins_desc_sorted, IH].
  Qed.
End SortDesc.

(** Sorting by a key that factors through [f] commutes with [map f]. *)
Lemma sort_desc_map {A B : Type} (f : A -> B) (key : B -> nat) (l : list A) :
  map f (sort_desc (fun a => key (f a)) l) = sort_desc key (map f l).
Proof.
  induction l as [| x r IH]; simpl; [reflexivity |].
  rewrite <- IH. clear IH. generalize (sort_desc (fun a => key (f a)) r) as s.
  induction s as [| y s IHs]; simpl; [reflexivity |].
  destruct (Nat.leb (key (f y)) (key (f x))); simpl; [reflexivity | rewrite IHs; reflexivity].
Qed.

Lemma sorted_desc_map {A B : Type} (f : A -> B) (key : B -> nat) (l : list A) :
  sorted_desc (fun a => key (f a)) l -> sorted_desc key (map f l).
Proof.
  induction l as [| x r IH]; simpl; [tauto |].
  intros [Hge Hs]. split; [| apply IH, Hs].
  apply Forall_map. exact Hge.
Qed.

(** ** The definition *)

(** Each mode with its canonical weight. *)
Fixpoint trip (L : modes) : list ((nat * nat) * nat) :=
  match L with
  | [] => []
  | m :: L' => (m, sprod (map fst L')) :: trip L'
  end.

Definition keyT (t : (nat * nat) * nat) : nat := snd (fst t).

Definition inv_mode (t : (nat * nat) * nat) : nat * nat := (fst (fst t), snd t).

Definition inverse (L : modes) : modes := map inv_mode (sort_desc keyT (trip L)).

Lemma map_fst_trip (L : modes) : map fst (trip L) = L.
Proof. induction L as [| m L IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma length_trip (L : modes) : length (trip L) = length L.
Proof. induction L as [| m L IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** ** The two maps on [[0, N)] *)

Definition phiL (L : modes) (x : nat) : nat := ev L (unflatten (map fst L) x).
Definition phiI (L : modes) (y : nat) : nat :=
  ev (inverse L) (unflatten (map fst (inverse L)) y).

(** ** Sums over modes, weights and indices together *)

Definition quad := ((nat * nat) * nat * nat)%type.

Definition sumD (R : list quad) : nat :=
  fold_right (fun q acc => snd q * snd (fst (fst q)) + acc) 0 R.
Definition sumW (R : list quad) : nat :=
  fold_right (fun q acc => snd q * snd (fst q) + acc) 0 R.
Definition cfits (q : quad) : Prop := snd q < fst (fst (fst q)).

Lemma sumD_perm (R R' : list quad) : Permutation R R' -> sumD R = sumD R'.
Proof. induction 1; simpl; lia. Qed.

Lemma sumW_perm (R R' : list quad) : Permutation R R' -> sumW R = sumW R'.
Proof. induction 1; simpl; lia. Qed.

Lemma ev_sumD (L : modes) (u : list nat) : ev L u = sumD (combine (trip L) u).
Proof.
  revert u. induction L as [| [n d] L IH]; intros u; [reflexivity |].
  destruct u as [| c u]; [reflexivity |]. simpl. rewrite IH. reflexivity.
Qed.

Lemma flat_sumW (L : modes) (u : list nat) :
  flat (map fst L) u = sumW (combine (trip L) u).
Proof.
  revert u. induction L as [| [n d] L IH]; intros u; [reflexivity |].
  destruct u as [| c u]; [reflexivity |]. simpl. rewrite IH. reflexivity.
Qed.

Lemma ev_sorted_D (R : list quad) : ev (map fst (map fst R)) (map snd R) = sumD R.
Proof.
  induction R as [| [[[n d] w] c] R IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma ev_sorted_W (R : list quad) : ev (map inv_mode (map fst R)) (map snd R) = sumW R.
Proof.
  induction R as [| [[[n d] w] c] R IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma coord_forall (L : modes) (u : list nat) :
  coord_ok L u -> Forall cfits (combine (trip L) u).
Proof.
  intros H. induction H as [| n s L c cs Hc Hcs IH]; simpl; [constructor |].
  constructor; [exact Hc | exact IH].
Qed.

Lemma coord_sorted_D (R : list quad) :
  Forall cfits R -> coord_ok (map fst (map fst R)) (map snd R).
Proof.
  induction R as [| [[[n d] w] c] R IH]; intros H; simpl; [constructor |].
  inversion H as [| ? ? Hq Hr]; subst. constructor; [exact Hq | apply IH, Hr].
Qed.

Lemma coord_sorted_W (R : list quad) :
  Forall cfits R -> coord_ok (map inv_mode (map fst R)) (map snd R).
Proof.
  induction R as [| [[[n d] w] c] R IH]; intros H; simpl; [constructor |].
  inversion H as [| ? ? Hq Hr]; subst. constructor; [exact Hq | apply IH, Hr].
Qed.

Lemma map_fst_combine {A B : Type} (a : list A) (b : list B) :
  length a = length b -> map fst (combine a b) = a.
Proof.
  revert b. induction a as [| x a IH]; intros b Hl; [reflexivity |].
  destruct b as [| y b]; [discriminate |]. simpl in *. rewrite IH by lia. reflexivity.
Qed.

(** ** Lemma 1, read in decreasing order: the canonical layout *)

Lemma sorted_strides_snoc (A : modes) (x : nat * nat) :
  sorted_strides A -> Forall (fun m => snd m <= snd x) A -> sorted_strides (A ++ [x]).
Proof.
  induction A as [| [n s] A IH]; intros Hs Hle; destruct x as [nx sx].
  - simpl. split; [constructor | exact I].
  - simpl in Hs |- *. destruct Hs as [Hge Hsa].
    inversion Hle as [| ? ? Hh Ht]; subst. simpl in Hh.
    split; [| apply IH; assumption].
    unfold strides_ge in *. apply Forall_app. split; [exact Hge |].
    constructor; [simpl; exact Hh | constructor].
Qed.

Lemma sorted_desc_rev (M : modes) : sorted_desc snd M -> sorted_strides (rev M).
Proof.
  induction M as [| x M IH]; simpl; [tauto |].
  intros [Hge Hs]. apply sorted_strides_snoc; [apply IH, Hs |].
  apply (Forall_perm_transfer _ M); [apply Permutation_rev | exact Hge].
Qed.

Lemma running_rev_canonical_eq (M : modes) : running 1 (rev M) -> M = canonical (map fst M).
Proof.
  induction M as [| [n s] M IH]; intros H; [reflexivity |].
  simpl in H. apply running_app in H. destruct H as [H1 H2].
  simpl in H2. destruct H2 as [Hs _].
  simpl. rewrite <- (IH H1). f_equal. f_equal.
  rewrite Hs, msize_rev, msize_sprod. lia.
Qed.

Lemma sorted_modes_canonical (L : modes) :
  sizes_ge2 L -> strides_pos L -> Dense 1 L ->
  map fst (sort_desc keyT (trip L)) = canonical (map fst (map fst (sort_desc keyT (trip L)))).
Proof.
  intros Hsz Hsp Hd.
  set (M := map fst (sort_desc keyT (trip L))).
  apply running_rev_canonical_eq.
  assert (Hp : Permutation L (rev M)).
  { transitivity M; [| apply Permutation_rev].
    unfold M. rewrite <- (map_fst_trip L) at 1. apply Permutation_map, sort_desc_perm. }
  assert (HS : sorted_strides (rev M)).
  { apply sorted_desc_rev. unfold M. apply (sorted_desc_map fst snd).
    apply sort_desc_sorted. }
  exact (proj1 (dense_iff_running_perm L (rev M) Hsz Hsp Hp HS) Hd).
Qed.

(** ** The theorems *)

Lemma sizes_ge2_forall (L : modes) : sizes_ge2 L -> Forall (fun n => 1 <= n) (map fst L).
Proof.
  intros H. apply Forall_map. eapply Forall_impl; [| exact H]. simpl. lia.
Qed.

Lemma perm_sorted (L : modes) : Permutation L (map fst (sort_desc keyT (trip L))).
Proof.
  rewrite <- (map_fst_trip L) at 1. apply Permutation_map, sort_desc_perm.
Qed.

Lemma map_fst_inverse (L : modes) :
  map fst (inverse L) = map fst (map fst (sort_desc keyT (trip L))).
Proof. unfold inverse. rewrite !map_map. reflexivity. Qed.

Lemma msize_inverse (L : modes) : msize (inverse L) = msize L.
Proof.
  rewrite (msize_sprod (inverse L)), map_fst_inverse, <- msize_sprod.
  symmetry. apply msize_perm, perm_sorted.
Qed.

(** [phiI] undoes [phiL]. *)
Theorem inverse_left (L : modes) (x : nat) :
  sizes_ge2 L -> strides_pos L -> Dense 1 L -> x < msize L ->
  phiI L (phiL L x) = x.
Proof.
  intros Hsz Hsp Hd Hx.
  set (S := map fst L).
  assert (Hpos : Forall (fun n => 1 <= n) S) by (apply sizes_ge2_forall, Hsz).
  rewrite msize_sprod in Hx. fold S in Hx.
  destruct (unflatten_spec S x Hpos Hx) as [Hu Hf].
  set (u := unflatten S x) in *.
  assert (HuL : coord_ok L u)
    by (apply (coord_ok_sizes (canonical S)); [rewrite map_fst_canonical; reflexivity | exact Hu]).
  set (T := sort_desc keyT (trip L)).
  set (Q := combine (trip L) u).
  set (R := sort_desc (fun a => keyT (fst a)) Q).
  assert (HlenQ : length (trip L) = length u)
    by (rewrite length_trip; symmetry; apply coord_ok_length, HuL).
  assert (HRT : map fst R = T).
  { unfold R, T. rewrite (sort_desc_map fst keyT Q). unfold Q.
    rewrite map_fst_combine by exact HlenQ. reflexivity. }
  assert (HQR : Permutation Q R) by apply sort_desc_perm.
  set (M := map fst T).
  set (SP := map fst M).
  assert (HMc : M = canonical SP) by (apply sorted_modes_canonical; assumption).
  assert (HposP : Forall (fun n => 1 <= n) SP).
  { unfold SP, M, T. apply sizes_ge2_forall.
    apply (Forall_perm_transfer _ L); [apply perm_sorted | exact Hsz]. }
  assert (Hfit : Forall cfits R)
    by (apply (Forall_perm_transfer _ Q); [exact HQR | apply coord_forall, HuL]).
  (* the reordered coordinate is a coordinate of the sorted shape *)
  assert (HcP : coord_ok (canonical SP) (map snd R)).
  { rewrite <- HMc. unfold M. rewrite <- HRT. apply coord_sorted_D, Hfit. }
  (* and it flattens there to L's value at u *)
  assert (HflatP : flat SP (map snd R) = ev L u).
  { rewrite <- ev_canonical, <- HMc. unfold M. rewrite <- HRT, ev_sorted_D.
    rewrite ev_sumD. symmetry. apply sumD_perm, HQR. }
  unfold phiI, phiL. fold S. fold u.
  rewrite map_fst_inverse. fold T. fold M. fold SP.
  rewrite <- HflatP, (unflatten_flat SP _ HposP HcP).
  unfold inverse. fold T. rewrite <- HRT, ev_sorted_W.
  rewrite <- (sumW_perm Q R HQR). unfold Q. rewrite <- flat_sumW. exact Hf.
Qed.

Lemma phiL_onto (L : modes) (y : nat) :
  sizes_ge2 L -> Dense 1 L -> y < msize L ->
  exists x, x < msize L /\ phiL L x = y.
Proof.
  intros Hsz [_ [Hsur _]] Hy.
  destruct (Hsur y Hy) as [u [Hu Ev]].
  set (S := map fst L).
  assert (Hpos : Forall (fun n => 1 <= n) S) by (apply sizes_ge2_forall, Hsz).
  assert (HuS : coord_ok (canonical S) u)
    by (apply (coord_ok_sizes L); [rewrite map_fst_canonical; reflexivity | exact Hu]).
  exists (flat S u). split.
  - rewrite msize_sprod. apply flat_lt; assumption.
  - unfold phiL. fold S. rewrite unflatten_flat by assumption. lia.
Qed.

(** [phiL] undoes [phiI]. *)
Theorem inverse_right (L : modes) (y : nat) :
  sizes_ge2 L -> strides_pos L -> Dense 1 L -> y < msize L ->
  phiL L (phiI L y) = y.
Proof.
  intros Hsz Hsp Hd Hy.
  destruct (phiL_onto L y Hsz Hd Hy) as [x [Hx <-]].
  rewrite inverse_left by assumption. reflexivity.
Qed.

Lemma phiL_lt (L : modes) (x : nat) :
  sizes_ge2 L -> Dense 1 L -> x < msize L -> phiL L x < msize L.
Proof.
  intros Hsz [Himg _] Hx.
  set (S := map fst L).
  assert (Hpos : Forall (fun n => 1 <= n) S) by (apply sizes_ge2_forall, Hsz).
  rewrite msize_sprod in Hx. fold S in Hx.
  destruct (unflatten_spec S x Hpos Hx) as [Hu _].
  assert (HuL : coord_ok L (unflatten S x))
    by (apply (coord_ok_sizes (canonical S)); [rewrite map_fst_canonical; reflexivity | exact Hu]).
  destruct (Himg _ HuL) as [k [Hk E]]. unfold phiL. fold S. lia.
Qed.

(** And [inverse L] is a dense bijection. *)
Theorem inverse_dense (L : modes) :
  sizes_ge2 L -> strides_pos L -> Dense 1 L -> Dense 1 (inverse L).
Proof.
  intros Hsz Hsp Hd.
  set (SP := map fst (inverse L)).
  assert (HposP : Forall (fun n => 1 <= n) SP).
  { unfold SP. rewrite map_fst_inverse. apply sizes_ge2_forall.
    apply (Forall_perm_transfer _ L); [apply perm_sorted | exact Hsz]. }
  assert (HN : sprod SP = msize L) by (unfold SP; rewrite <- msize_sprod; apply msize_inverse).
  assert (Hsame : map fst (canonical SP) = map fst (inverse L))
    by (rewrite map_fst_canonical; reflexivity).
  (* a coordinate of inverse L is the unflattening of its flattening *)
  assert (Hco : forall c, coord_ok (inverse L) c ->
            flat SP c < msize L /\ ev (inverse L) c = phiI L (flat SP c)).
  { intros c Hc.
    assert (HcP : coord_ok (canonical SP) c)
      by (apply (coord_ok_sizes (inverse L)); [symmetry; exact Hsame | exact Hc]).
    split; [rewrite <- HN; apply flat_lt; assumption |].
    unfold phiI. fold SP. rewrite unflatten_flat by assumption. reflexivity. }
  unfold Dense. rewrite msize_inverse. split; [| split].
  - intros c Hc. destruct (Hco c Hc) as [Hlt E].
    destruct (phiL_onto L _ Hsz Hd Hlt) as [x [Hx Hxy]].
    exists x. split; [exact Hx |]. rewrite E, <- Hxy, inverse_left by assumption. lia.
  - intros k Hk.
    assert (Hy : phiL L k < sprod SP) by (rewrite HN; apply phiL_lt; assumption).
    destruct (unflatten_spec SP _ HposP Hy) as [Hc Hf].
    exists (unflatten SP (phiL L k)). split.
    + apply (coord_ok_sizes (canonical SP)); [exact Hsame | exact Hc].
    + pose proof (inverse_left L k Hsz Hsp Hd Hk) as E.
      unfold phiI in E. fold SP in E. lia.
  - intros c1 c2 H1 H2 E.
    destruct (Hco c1 H1) as [Hl1 E1]. destruct (Hco c2 H2) as [Hl2 E2].
    rewrite E1, E2 in E.
    apply (f_equal (phiL L)) in E. rewrite !inverse_right in E by assumption.
    apply (flat_inj SP); [exact HposP | | | exact E];
      apply (coord_ok_sizes (inverse L)); try (symmetry; exact Hsame); assumption.
Qed.
