(** * The operations of Section 3

    What the paper claims of each operation, on flat layouts:

    - [canonical S] is the row-major flattening of Definition 1, and a
      dense bijection ([ev_canonical], [canonical_dense]);
    - [split (n:d) S] is the mode [n:d] read through that flattening
      ([split_correct]);
    - [divide L S] is [L] precomposed with [(t_i, b_i) |-> b_i k_i + t_i],
      a bijection of coordinates ([divide_correct], [divide_onto],
      [divide_inj]);
    - [repeat L A] and [interleave L A] are dense bijections when [L] and
      [A] are ([repeat_dense], [interleave_dense]), with [repeat] taking
      the cosize of [L] as the paper defines it ([cosize_dense]);
    - [broadcast L S] is valid but not write-valid ([broadcast_valid],
      [broadcast_not_write_valid]).

    [Inverse] and [Swizzle] cover [inverse] and the swizzle facts. *)

From Stdlib Require Import Arith Lia List Permutation.
From LayoutAlgebra Require Import Dense DenseSort.
Import ListNotations.

(** ** Groundwork on modes *)

Lemma coord_ok_length (L : modes) (cs : list nat) :
  coord_ok L cs -> length cs = length L.
Proof. induction 1; simpl; congruence. Qed.

Lemma coord_ok_app (A B : modes) (a b : list nat) :
  coord_ok A a -> coord_ok B b -> coord_ok (A ++ B) (a ++ b).
Proof. intros HA HB. induction HA; simpl; [exact HB | constructor; assumption]. Qed.

Lemma coord_ok_app_inv (A B : modes) (l : list nat) :
  coord_ok (A ++ B) l -> exists a b, l = a ++ b /\ coord_ok A a /\ coord_ok B b.
Proof.
  revert l. induction A as [| [n s] A IH]; intros l H.
  - exists [], l. split; [reflexivity | split; [constructor | exact H]].
  - simpl in H. inversion H as [| n' s' L' x c Hx Hc]; subst.
    destruct (IH c Hc) as [a [b [-> [Ha Hb]]]].
    exists (x :: a), b.
    split; [reflexivity | split; [constructor; assumption | exact Hb]].
Qed.

Lemma ev_app (A B : modes) (a b : list nat) :
  length A = length a -> ev (A ++ B) (a ++ b) = ev A a + ev B b.
Proof.
  revert a. induction A as [| [n s] A IH]; intros a Hl.
  - destruct a; [reflexivity | discriminate].
  - destruct a as [| x a]; [discriminate |].
    simpl in Hl |- *. rewrite IH by lia. lia.
Qed.

Lemma msize_app (A B : modes) : msize (A ++ B) = msize A * msize B.
Proof. induction A as [| [n s] A IH]; simpl; [lia | rewrite IH; ring]. Qed.

(** Every stride multiplied by [k]. *)
Definition scale (k : nat) (L : modes) : modes := map (fun m => (fst m, k * snd m)) L.

Lemma msize_scale (k : nat) (L : modes) : msize (scale k L) = msize L.
Proof. induction L as [| [n s] L IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma ev_scale (k : nat) (L : modes) (cs : list nat) : ev (scale k L) cs = k * ev L cs.
Proof.
  revert cs. induction L as [| [n s] L IH]; intros cs; [simpl; lia |].
  destruct cs as [| c cs]; simpl; [lia | rewrite IH; ring].
Qed.

Lemma coord_ok_scale (k : nat) (L : modes) (cs : list nat) :
  coord_ok (scale k L) cs <-> coord_ok L cs.
Proof.
  revert cs. induction L as [| [n s] L IH]; intros cs; simpl.
  - split; intros H; inversion H; constructor.
  - split; intros H; inversion H as [| n' s' L' c cs' Hc Hcs]; subst;
      constructor; [exact Hc | apply IH; exact Hcs | exact Hc | apply IH; exact Hcs].
Qed.

Lemma sizes_pos_perm (L L' : modes) : Permutation L L' -> sizes_pos L -> sizes_pos L'.
Proof. apply Forall_perm_transfer. Qed.

(** ** canonical *)

Fixpoint sprod (S : list nat) : nat :=
  match S with [] => 1 | n :: S' => n * sprod S' end.

(** The strides are the products of the sizes to the right. *)
Fixpoint canonical (S : list nat) : modes :=
  match S with
  | [] => []
  | n :: S' => (n, sprod S') :: canonical S'
  end.

(** Definition 1's row-major flattening of a flat coordinate. *)
Fixpoint flat (S : list nat) (c : list nat) : nat :=
  match S, c with
  | _ :: S', x :: c' => x * sprod S' + flat S' c'
  | _, _ => 0
  end.

Theorem ev_canonical (S c : list nat) : ev (canonical S) c = flat S c.
Proof.
  revert c. induction S as [| n S IH]; intros c; [reflexivity |].
  destruct c as [| x c]; [reflexivity |]. simpl. rewrite IH. reflexivity.
Qed.

Lemma msize_canonical (S : list nat) : msize (canonical S) = sprod S.
Proof. induction S as [| n S IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma running_app (w : nat) (A B : modes) :
  running w (A ++ B) <-> running w A /\ running (w * msize A) B.
Proof.
  revert w. induction A as [| [n s] A IH]; intros w; simpl.
  - rewrite Nat.mul_1_r. tauto.
  - rewrite IH. rewrite Nat.mul_assoc. tauto.
Qed.

Lemma msize_rev (L : modes) : msize (rev L) = msize L.
Proof. symmetry. apply msize_perm, Permutation_rev. Qed.

(** Read from the right, the canonical strides are running products. *)
Lemma running_rev_canonical (S : list nat) : running 1 (rev (canonical S)).
Proof.
  induction S as [| n S IH]; simpl; [exact I |].
  apply running_app. split; [exact IH |].
  simpl. rewrite msize_rev, msize_canonical. split; [lia | exact I].
Qed.

Lemma sizes_pos_canonical (S : list nat) :
  Forall (fun n => 1 <= n) S -> sizes_pos (canonical S).
Proof.
  induction S as [| n S IH]; intros H; [constructor |].
  inversion H; subst. constructor; [simpl; assumption | apply IH; assumption].
Qed.

Theorem canonical_dense (S : list nat) :
  Forall (fun n => 1 <= n) S -> Dense 1 (canonical S).
Proof.
  intros H.
  apply (dense_perm 1 (rev (canonical S))); [apply Permutation_sym, Permutation_rev |].
  apply running_dense; [lia | | apply running_rev_canonical].
  apply (sizes_pos_perm (canonical S)); [apply Permutation_rev |].
  apply sizes_pos_canonical, H.
Qed.

(** ** split *)

Definition split_mode (d : nat) (S : list nat) : modes := scale d (canonical S).

(** [split (n:d) S] at [c] is [n:d] at the flattening of [c]. *)
Theorem split_correct (d : nat) (S c : list nat) :
  ev (split_mode d S) c = ev [(sprod S, d)] [flat S c].
Proof. unfold split_mode. rewrite ev_scale, ev_canonical. simpl. ring. Qed.

Lemma msize_split (d : nat) (S : list nat) : msize (split_mode d S) = sprod S.
Proof. unfold split_mode. rewrite msize_scale. apply msize_canonical. Qed.

(** ** divide *)

Fixpoint tile_part (L : modes) (S : list nat) : modes :=
  match L, S with
  | (_, d) :: L', k :: S' => (k, d) :: tile_part L' S'
  | _, _ => []
  end.

Fixpoint rest_part (L : modes) (S : list nat) : modes :=
  match L, S with
  | (n, d) :: L', k :: S' => (n / k, k * d) :: rest_part L' S'
  | _, _ => []
  end.

(** The tile modes, then the modes indexing which tile. *)
Definition divide (L : modes) (S : list nat) : modes := tile_part L S ++ rest_part L S.

(** One tile size per mode, each positive and dividing its mode. *)
Fixpoint tiles_ok (L : modes) (S : list nat) : Prop :=
  match L, S with
  | [], [] => True
  | (n, _) :: L', k :: S' => 1 <= k /\ Nat.divide k n /\ tiles_ok L' S'
  | _, _ => False
  end.

(** [(t_i, b_i) |-> b_i k_i + t_i]. *)
Fixpoint recombine (S t b : list nat) : list nat :=
  match S, t, b with
  | k :: S', x :: t', y :: b' => (y * k + x) :: recombine S' t' b'
  | _, _, _ => []
  end.

Lemma msize_divide (L : modes) (S : list nat) :
  tiles_ok L S -> msize (divide L S) = msize L.
Proof.
  unfold divide. rewrite msize_app. revert S.
  induction L as [| [n d] L IH]; intros S H; destruct S as [| k S]; simpl in H |- *;
    try contradiction; [reflexivity |].
  destruct H as [Hk [[q Hq] HS]].
  specialize (IH S HS).
  rewrite Hq, Nat.div_mul by lia. rewrite <- IH. ring.
Qed.

Lemma divide_parts (L : modes) (S t b : list nat) :
  tiles_ok L S -> coord_ok (tile_part L S) t -> coord_ok (rest_part L S) b ->
  coord_ok L (recombine S t b)
  /\ ev (tile_part L S) t + ev (rest_part L S) b = ev L (recombine S t b).
Proof.
  revert S t b.
  induction L as [| [n d] L IH]; intros S t b H Ht Hb;
    destruct S as [| k S]; simpl in H; try contradiction.
  - inversion Ht; inversion Hb; subst. split; [constructor | reflexivity].
  - destruct H as [Hk [[q Hq] HS]].
    simpl in Ht, Hb.
    inversion Ht as [| k0 d0 L0 x t' Hx Ht']; subst.
    inversion Hb as [| q0 kd0 L1 y b' Hy Hb']; subst.
    rewrite Nat.div_mul in Hy by lia.
    destruct (IH S t' b' HS Ht' Hb') as [Hc He].
    split.
    + simpl. constructor; [nia | exact Hc].
    + simpl. rewrite <- He. ring.
Qed.

(** [divide L S] at [(t, b)] is [L] at [b_i k_i + t_i]. *)
Theorem divide_correct (L : modes) (S t b : list nat) :
  tiles_ok L S -> coord_ok (tile_part L S) t -> coord_ok (rest_part L S) b ->
  coord_ok L (recombine S t b)
  /\ ev (divide L S) (t ++ b) = ev L (recombine S t b).
Proof.
  intros H Ht Hb. destruct (divide_parts L S t b H Ht Hb) as [Hc He].
  split; [exact Hc |]. unfold divide. rewrite ev_app; [exact He |].
  symmetry. apply coord_ok_length, Ht.
Qed.

(** Every coordinate of [L] is reached: [t_i = c_i mod k_i],
    [b_i = c_i / k_i]. *)
Theorem divide_onto (L : modes) (S c : list nat) :
  tiles_ok L S -> coord_ok L c ->
  exists t b, coord_ok (tile_part L S) t /\ coord_ok (rest_part L S) b
              /\ recombine S t b = c.
Proof.
  revert S c.
  induction L as [| [n d] L IH]; intros S c H Hc;
    destruct S as [| k S]; simpl in H; try contradiction.
  - inversion Hc; subst. exists [], []. split; [constructor | split; [constructor | reflexivity]].
  - destruct H as [Hk [[q Hq] HS]].
    inversion Hc as [| n0 d0 L0 x c' Hx Hc']; subst.
    destruct (IH S c' HS Hc') as [t [b [Ht [Hb Hr]]]].
    exists (x mod k :: t), (x / k :: b). split; [| split].
    + simpl. constructor; [apply Nat.mod_upper_bound; lia | exact Ht].
    + simpl. constructor; [| exact Hb].
      rewrite Nat.div_mul by lia. apply Nat.Div0.div_lt_upper_bound. nia.
    + simpl. rewrite Hr. f_equal.
      rewrite (Nat.div_mod_eq x k) at 3. ring.
Qed.

(** And no coordinate twice. *)
Theorem divide_inj (L : modes) (S t b t' b' : list nat) :
  tiles_ok L S ->
  coord_ok (tile_part L S) t -> coord_ok (rest_part L S) b ->
  coord_ok (tile_part L S) t' -> coord_ok (rest_part L S) b' ->
  recombine S t b = recombine S t' b' -> t = t' /\ b = b'.
Proof.
  revert S t b t' b'.
  induction L as [| [n d] L IH]; intros S t b t' b' H Ht Hb Ht' Hb' Heq;
    destruct S as [| k S]; simpl in H; try contradiction.
  - inversion Ht; inversion Hb; inversion Ht'; inversion Hb'; subst.
    split; reflexivity.
  - destruct H as [Hk [_ HS]]. simpl in Ht, Hb, Ht', Hb'.
    inversion Ht as [| k0 d0 L0 x t1 Hx Ht1]; subst.
    inversion Hb as [| q0 kd0 L1 y b1 Hy Hb1]; subst.
    inversion Ht' as [| k2 d2 L2 x' t2 Hx' Ht2]; subst.
    inversion Hb' as [| q3 kd3 L3 y' b2 Hy' Hb2]; subst.
    simpl in Heq. injection Heq as Hhd Htl.
    destruct (IH S t1 b1 t2 b2 HS Ht1 Hb1 Ht2 Hb2 Htl) as [-> ->].
    (* y k + x = y' k + x' with x, x' < k *)
    assert (Hyy : y = y').
    { destruct (Nat.lt_trichotomy y y') as [Hlt | [E | Hgt]]; [nia | exact E | nia]. }
    subst y'. assert (x = x') by lia. subst x'. split; reflexivity.
Qed.

(** ** repeat and interleave *)

(** Stacking: [B] runs inside, [A] across copies of it. *)
Lemma dense_stack (A B : modes) :
  Dense 1 A -> Dense 1 B -> Dense 1 (scale (msize B) A ++ B).
Proof.
  intros [ImgA [SurA InjA]] [ImgB [SurB InjB]].
  assert (Hlen : forall a, coord_ok (scale (msize B) A) a ->
                   length (scale (msize B) A) = length a)
    by (intros a Ha; symmetry; apply coord_ok_length, Ha).
  unfold Dense. rewrite msize_app, msize_scale.
  split; [| split].
  - intros cs Hcs. destruct (coord_ok_app_inv _ _ _ Hcs) as [a [b [-> [Ha Hb]]]].
    rewrite ev_app by (apply Hlen, Ha). rewrite ev_scale.
    apply coord_ok_scale in Ha.
    destruct (ImgA a Ha) as [ka [Hka Ea]]. destruct (ImgB b Hb) as [kb [Hkb Eb]].
    exists (msize B * ka + kb). split; [nia | rewrite Ea, Eb; ring].
  - intros k Hk.
    assert (HmB : 1 <= msize B) by (destruct (msize B); nia).
    destruct (SurA (k / msize B)) as [a [Ha Ea]];
      [apply Nat.Div0.div_lt_upper_bound; nia |].
    destruct (SurB (k mod msize B)) as [b [Hb Eb]]; [apply Nat.mod_upper_bound; lia |].
    exists (a ++ b). split.
    + apply coord_ok_app; [apply coord_ok_scale, Ha | exact Hb].
    + rewrite ev_app by (apply Hlen, coord_ok_scale, Ha).
      rewrite ev_scale, Ea, Eb.
      rewrite (Nat.div_mod_eq k (msize B)) at 3. ring.
  - intros c1 c2 H1 H2 Heq.
    destruct (coord_ok_app_inv _ _ _ H1) as [a1 [b1 [-> [Ha1 Hb1]]]].
    destruct (coord_ok_app_inv _ _ _ H2) as [a2 [b2 [-> [Ha2 Hb2]]]].
    rewrite !ev_app in Heq by (apply Hlen; assumption).
    rewrite !ev_scale in Heq.
    apply coord_ok_scale in Ha1. apply coord_ok_scale in Ha2.
    destruct (ImgA a1 Ha1) as [ka1 [Hk1 Ea1]]. destruct (ImgA a2 Ha2) as [ka2 [Hk2 Ea2]].
    destruct (ImgB b1 Hb1) as [kb1 [Hj1 Eb1]]. destruct (ImgB b2 Hb2) as [kb2 [Hj2 Eb2]].
    rewrite Ea1, Ea2, Eb1, Eb2 in Heq.
    assert (Hka : ka1 = ka2).
    { destruct (Nat.lt_trichotomy ka1 ka2) as [Hlt | [E | Hgt]]; [nia | exact E | nia]. }
    subst ka2. assert (kb1 = kb2) by lia. subst kb2.
    rewrite (InjA a1 a2 Ha1 Ha2 ltac:(rewrite Ea1, Ea2; reflexivity)).
    rewrite (InjB b1 b2 Hb1 Hb2 ltac:(rewrite Eb1, Eb2; reflexivity)).
    reflexivity.
Qed.

(** The cosize: the least [N] with the image inside [[0, N)]. *)
Definition IsCosize (L : modes) (N : nat) : Prop :=
  (forall cs, coord_ok L cs -> ev L cs < N)
  /\ (forall N', (forall cs, coord_ok L cs -> ev L cs < N') -> N <= N').

(** For a dense bijection it is the size. *)
Theorem cosize_dense (L : modes) (N : nat) : Dense 1 L -> IsCosize L N -> N = msize L.
Proof.
  intros [Img [Sur _]] [Hbound Hleast].
  assert (Hle : N <= msize L).
  { apply Hleast. intros cs Hcs. destruct (Img cs Hcs) as [k [Hk E]]. lia. }
  destruct (msize L) as [| m] eqn:Hm; [lia |].
  destruct (Sur m ltac:(lia)) as [cs [Hcs E]].
  specialize (Hbound cs Hcs). lia.
Qed.

(** [repeat L A] with the cosize of [L] as the paper defines it. *)
Definition repeat (N : nat) (L A : modes) : modes := scale N A ++ L.

Theorem repeat_dense (N : nat) (L A : modes) :
  Dense 1 L -> Dense 1 A -> IsCosize L N -> Dense 1 (repeat N L A).
Proof.
  intros HL HA HN. unfold repeat. rewrite (cosize_dense L N HL HN).
  apply dense_stack; assumption.
Qed.

(** [interleave L A]: the copies interleaved element by element. *)
Definition interleave (L A : modes) : modes := A ++ scale (msize A) L.

Theorem interleave_dense (L A : modes) :
  Dense 1 L -> Dense 1 A -> Dense 1 (interleave L A).
Proof.
  intros HL HA. unfold interleave.
  apply (dense_perm 1 (scale (msize A) L ++ A)); [apply Permutation_app_comm |].
  apply dense_stack; assumption.
Qed.

(** ** broadcast, and validity with replicated modes *)

(** A stride is a positive integer or the mark [None] for replication. *)
Definition omodes := list (nat * option nat).

Inductive ocoord_ok : omodes -> list nat -> Prop :=
| ocoord_nil : ocoord_ok [] []
| ocoord_cons : forall n s L c cs,
    c < n -> ocoord_ok L cs -> ocoord_ok ((n, s) :: L) (c :: cs).

Fixpoint oev (L : omodes) (cs : list nat) : nat :=
  match L, cs with
  | (_, Some s) :: L', c :: cs' => c * s + oev L' cs'
  | (_, None) :: L', _ :: cs' => oev L' cs'
  | _, _ => 0
  end.

(** Declared replicas: equal at every mode whose stride is an integer. *)
Fixpoint replica (L : omodes) (c c' : list nat) : Prop :=
  match L, c, c' with
  | [], [], [] => True
  | (_, Some _) :: L', x :: r, x' :: r' => x = x' /\ replica L' r r'
  | (_, None) :: L', _ :: r, _ :: r' => replica L' r r'
  | _, _, _ => False
  end.

(** Definition 7, for a layout into physical space. *)
Definition valid (L : omodes) : Prop :=
  forall c c', ocoord_ok L c -> ocoord_ok L c' -> oev L c = oev L c' -> replica L c c'.

Definition write_valid (L : omodes) : Prop :=
  forall c c', ocoord_ok L c -> ocoord_ok L c' -> oev L c = oev L c' -> c = c'.

Definition broadcast (L : omodes) (S : list nat) : omodes :=
  map (fun n => (n, None)) S ++ L.

Lemma ocoord_ok_app_inv (A B : omodes) (l : list nat) :
  ocoord_ok (A ++ B) l -> exists a b, l = a ++ b /\ ocoord_ok A a /\ ocoord_ok B b.
Proof.
  revert l. induction A as [| [n s] A IH]; intros l H.
  - exists [], l. split; [reflexivity | split; [constructor | exact H]].
  - simpl in H. inversion H as [| n' s' L' x c Hx Hc]; subst.
    destruct (IH c Hc) as [a [b [-> [Ha Hb]]]].
    exists (x :: a), b.
    split; [reflexivity | split; [constructor; assumption | exact Hb]].
Qed.

Lemma ocoord_ok_app (A B : omodes) (a b : list nat) :
  ocoord_ok A a -> ocoord_ok B b -> ocoord_ok (A ++ B) (a ++ b).
Proof. intros HA HB. induction HA; simpl; [exact HB | constructor; assumption]. Qed.

Lemma oev_broadcast (S : list nat) (L : omodes) (a v : list nat) :
  ocoord_ok (map (fun n => (n, None)) S) a ->
  oev (broadcast L S) (a ++ v) = oev L v.
Proof.
  unfold broadcast. revert a. induction S as [| n S IH]; intros a Ha.
  - inversion Ha; reflexivity.
  - simpl in Ha. inversion Ha as [| n0 s0 L0 x a' Hx Ha']; subst.
    simpl. apply IH, Ha'.
Qed.

Lemma replica_broadcast (S : list nat) (L : omodes) (a a' v v' : list nat) :
  ocoord_ok (map (fun n => (n, None)) S) a ->
  ocoord_ok (map (fun n => (n, None)) S) a' ->
  replica L v v' -> replica (broadcast L S) (a ++ v) (a' ++ v').
Proof.
  unfold broadcast. revert a a'. induction S as [| n S IH]; intros a a' Ha Ha' Hr.
  - inversion Ha; inversion Ha'; exact Hr.
  - simpl in Ha, Ha'.
    inversion Ha as [| n0 s0 L0 x r Hx Hr0]; subst.
    inversion Ha' as [| n1 s1 L1 x' r' Hx' Hr1]; subst.
    simpl. apply IH; assumption.
Qed.

(** Coordinates that collide differ only in the broadcast modes, or in
    replicated modes of [L]. *)
Theorem broadcast_valid (L : omodes) (S : list nat) :
  valid L -> valid (broadcast L S).
Proof.
  intros HL c c' Hc Hc' Heq.
  destruct (ocoord_ok_app_inv _ _ _ Hc) as [a [v [-> [Ha Hv]]]].
  destruct (ocoord_ok_app_inv _ _ _ Hc') as [a' [v' [-> [Ha' Hv']]]].
  rewrite !oev_broadcast in Heq by assumption.
  apply replica_broadcast; [exact Ha | exact Ha' | apply HL; assumption].
Qed.

Fixpoint ozeros (S : list nat) : list nat :=
  match S with [] => [] | _ :: S' => 0 :: ozeros S' end.

Lemma ozeros_ok (S : list nat) :
  Forall (fun n => 1 <= n) S -> ocoord_ok (map (fun n => (n, None)) S) (ozeros S).
Proof.
  induction S as [| n S IH]; intros H; [constructor |].
  inversion H; subst. simpl. constructor; [lia | apply IH; assumption].
Qed.

(** Two copies at the same address: a store through it would race. *)
Theorem broadcast_not_write_valid (L : omodes) (S : list nat) (v : list nat) :
  Forall (fun n => 1 <= n) S -> (exists n, In n S /\ 2 <= n) -> ocoord_ok L v ->
  ~ write_valid (broadcast L S).
Proof.
  intros Hpos [n [Hin Hn]] Hv Hwv.
  destruct (in_split n S Hin) as [S1 [S2 ->]].
  apply Forall_app in Hpos. destruct Hpos as [H1 H2].
  inversion H2 as [| ? ? Hn1 H2']; subst.
  set (a0 := ozeros S1 ++ 0 :: ozeros S2).
  set (a1 := ozeros S1 ++ 1 :: ozeros S2).
  assert (Ha : forall x, x < n ->
            ocoord_ok (map (fun n => (n, None)) (S1 ++ n :: S2)) (ozeros S1 ++ x :: ozeros S2)).
  { intros x Hx. rewrite map_app. apply ocoord_ok_app; [apply ozeros_ok, H1 |].
    simpl. constructor; [exact Hx | apply ozeros_ok, H2']. }
  assert (Heq := Hwv (a0 ++ v) (a1 ++ v)).
  rewrite !oev_broadcast in Heq by (apply Ha; lia).
  specialize (Heq ltac:(apply ocoord_ok_app; [apply Ha; lia | exact Hv])
                  ltac:(apply ocoord_ok_app; [apply Ha; lia | exact Hv]) eq_refl).
  apply app_inv_tail in Heq. unfold a0, a1 in Heq.
  apply app_inv_head in Heq. discriminate.
Qed.
