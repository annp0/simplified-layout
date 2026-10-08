(** * Swizzles

    Definition 4's swizzle,

      sigma(x) = x xor (((x >> src) & (2^b - 1)) << dst),

    and the two facts the paper uses about it:

    - with its two fields disjoint it is an involution, so a bijection,
      and distinct addresses stay distinct ([swizzle_involutive],
      [swizzle_inj]);
    - when [repeat] copies a swizzled layout whose cosize is [2^p] and
      both fields lie below [p], every copy is swizzled alike:
      [sigma (2^p a + x) = 2^p a + sigma x] ([swizzle_repeat]). *)

From Stdlib Require Import ZArith Lia Bool.

Open Scope Z_scope.

Definition swz_mask (b src dst x : Z) : Z :=
  Z.shiftl (Z.land (Z.shiftr x src) (Z.ones b)) dst.

Definition swizzle (b src dst x : Z) : Z := Z.lxor x (swz_mask b src dst x).

Definition fields_disjoint (b src dst : Z) : Prop := src + b <= dst \/ dst + b <= src.

(** The mask carries bit [i - dst + src] of [x] into bit [i], for [i]
    in the destination field, and is zero elsewhere. *)
Lemma testbit_mask (b src dst x i : Z) :
  0 <= b -> 0 <= src -> 0 <= i ->
  Z.testbit (swz_mask b src dst x) i
  = if (dst <=? i) && (i <? dst + b) then Z.testbit x (i - dst + src) else false.
Proof.
  intros Hb Hs Hi. unfold swz_mask. rewrite Z.shiftl_spec by exact Hi.
  destruct (Z.leb_spec dst i) as [Hd | Hd]; simpl.
  - rewrite Z.land_spec, Z.shiftr_spec by lia.
    rewrite Z.testbit_ones by exact Hb.
    replace (0 <=? i - dst) with true by (symmetry; apply Z.leb_le; lia).
    destruct (Z.ltb_spec (i - dst) b) as [H1 | H1];
      destruct (Z.ltb_spec i (dst + b)) as [H2 | H2]; try lia; simpl;
      rewrite ?andb_true_r, ?andb_false_r; reflexivity.
  - apply Z.testbit_neg_r. lia.
Qed.

(** ** A swizzle with disjoint fields is an involution *)

(** Swizzling changes only the destination field, which the mask does
    not read. *)
Lemma mask_swizzle (b src dst x : Z) :
  0 <= b -> 0 <= src -> 0 <= dst -> fields_disjoint b src dst ->
  swz_mask b src dst (swizzle b src dst x) = swz_mask b src dst x.
Proof.
  intros Hb Hs Hd Hdisj. apply Z.bits_inj'. intros i Hi.
  rewrite !testbit_mask by assumption.
  destruct ((dst <=? i) && (i <? dst + b)) eqn:E; [| reflexivity].
  apply andb_true_iff in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  unfold swizzle. rewrite Z.lxor_spec, testbit_mask by lia.
  replace ((dst <=? i - dst + src) && (i - dst + src <? dst + b)) with false.
  - simpl. apply xorb_false_r.
  - symmetry. apply andb_false_iff. destruct Hdisj as [H | H].
    + left. apply Z.leb_gt. lia.
    + right. apply Z.ltb_ge. lia.
Qed.

Theorem swizzle_involutive (b src dst x : Z) :
  0 <= b -> 0 <= src -> 0 <= dst -> fields_disjoint b src dst ->
  swizzle b src dst (swizzle b src dst x) = x.
Proof.
  intros Hb Hs Hd Hdisj.
  unfold swizzle at 1. rewrite mask_swizzle by assumption.
  unfold swizzle. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r.
  reflexivity.
Qed.

Corollary swizzle_inj (b src dst x y : Z) :
  0 <= b -> 0 <= src -> 0 <= dst -> fields_disjoint b src dst ->
  swizzle b src dst x = swizzle b src dst y -> x = y.
Proof.
  intros Hb Hs Hd Hdisj H.
  apply (f_equal (swizzle b src dst)) in H.
  rewrite !swizzle_involutive in H by assumption. exact H.
Qed.

(** ** A swizzle below [2^p] commutes with a copy offset of [2^p] *)

Lemma testbit_low (p a z i : Z) :
  0 <= p -> 0 <= i < p -> Z.testbit (2 ^ p * a + z) i = Z.testbit z i.
Proof.
  intros Hp Hi.
  rewrite <- (Z.mod_pow2_bits_low (2 ^ p * a + z) p i) by lia.
  rewrite <- (Z.mod_pow2_bits_low z p i) by lia.
  f_equal. rewrite Z.add_comm, Z.mul_comm, Z.mod_add; [reflexivity |].
  apply Z.pow_nonzero; lia.
Qed.

Lemma testbit_high (p a z i : Z) :
  0 <= p -> 0 <= z < 2 ^ p -> p <= i ->
  Z.testbit (2 ^ p * a + z) i = Z.testbit a (i - p).
Proof.
  intros Hp Hz Hi.
  replace (Z.testbit (2 ^ p * a + z) i)
    with (Z.testbit (Z.shiftr (2 ^ p * a + z) p) (i - p))
    by (rewrite Z.shiftr_spec by lia; f_equal; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  f_equal. rewrite Z.add_comm, Z.mul_comm, Z.div_add by (apply Z.pow_nonzero; lia).
  rewrite Z.div_small by lia. lia.
Qed.

Lemma testbit_above (p z i : Z) :
  0 <= p -> 0 <= z < 2 ^ p -> p <= i -> Z.testbit z i = false.
Proof.
  intros Hp Hz Hi. rewrite <- (Z.mod_small z (2 ^ p)) by lia.
  apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma below_pow2 (p z : Z) :
  0 <= p -> 0 <= z -> (forall i, p <= i -> Z.testbit z i = false) -> z < 2 ^ p.
Proof.
  intros Hp Hz H.
  assert (E : z = z mod 2 ^ p).
  { apply Z.bits_inj'. intros i Hi. destruct (Z.lt_ge_cases i p).
    - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
    - rewrite Z.mod_pow2_bits_high by lia. apply H. lia. }
  rewrite E.
  pose proof (Z.mod_pos_bound z (2 ^ p) ltac:(apply Z.pow_pos_nonneg; lia)). lia.
Qed.

Theorem swizzle_repeat (b src dst p a x : Z) :
  0 <= b -> 0 <= src -> 0 <= dst -> src + b <= p -> dst + b <= p ->
  0 <= x < 2 ^ p ->
  swizzle b src dst (2 ^ p * a + x) = 2 ^ p * a + swizzle b src dst x.
Proof.
  intros Hb Hs Hd Hsp Hdp Hx.
  assert (Hp : 0 <= p) by lia.
  (* the mask reads only bits below p, where the copy offset is invisible *)
  assert (Hm : swz_mask b src dst (2 ^ p * a + x) = swz_mask b src dst x).
  { apply Z.bits_inj'. intros i Hi. rewrite !testbit_mask by assumption.
    destruct ((dst <=? i) && (i <? dst + b)) eqn:E; [| reflexivity].
    apply andb_true_iff in E. destruct E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    apply testbit_low; lia. }
  set (m := swz_mask b src dst x) in *.
  assert (Hm0 : 0 <= m).
  { unfold m, swz_mask. apply Z.shiftl_nonneg, Z.land_nonneg. left.
    apply Z.shiftr_nonneg. lia. }
  (* and it writes only bits below p *)
  assert (Hmhi : forall i, p <= i -> Z.testbit m i = false).
  { intros i Hi. unfold m. rewrite testbit_mask by lia.
    replace ((dst <=? i) && (i <? dst + b)) with false; [reflexivity |].
    symmetry. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
  assert (Hz : 0 <= Z.lxor x m < 2 ^ p).
  { assert (H0 : 0 <= Z.lxor x m) by (apply Z.lxor_nonneg; split; intros; lia).
    split; [exact H0 |].
    apply below_pow2; [lia | exact H0 |].
    intros i Hi. rewrite Z.lxor_spec, (testbit_above p x i), Hmhi by lia.
    reflexivity. }
  unfold swizzle. rewrite Hm. fold m.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec.
  destruct (Z.lt_ge_cases i p).
  - rewrite !testbit_low by lia. rewrite Z.lxor_spec. reflexivity.
  - rewrite !testbit_high by lia. rewrite Hmhi by lia. apply xorb_false_r.
Qed.
