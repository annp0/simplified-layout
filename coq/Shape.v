(** * From a chain back to a shape with strides

    [Recognize.scan_sound] delivers the FLOOR form. A layout is the
    DIGIT form, so to read the scan's output as a layout we invert the
    change of variables of [Chain.coeffs]: given a chain
    [1 = w_1 | ... | w_k | n] with floor coefficients [a_j], the shape
    has radices [m_j = w_{j+1}/w_j] (with [w_{k+1} = n]) and strides
    [s_j = a_j + m_{j-1} s_{j-1}].

    The result is [scan_sound_layout]: if the scan accepts, [g] really
    is the index function of a flat shape of size [n]. *)

From Coq Require Import Arith Lia ZArith List.
From LayoutAlgebra Require Import Floors Chain Recognize.
Import ListNotations.

Open Scope Z_scope.

(** The next weight in the chain, [n] past the end. *)
Definition next_w (n : nat) (rest : list (nat * Z)) : nat :=
  match rest with
  | [] => n
  | (w', _) :: _ => w'
  end.

(** [s_j = a_j + m_{j-1} s_{j-1}], threaded left to right. *)
Fixpoint shape_of (n : nat) (prev : Z) (ws : list (nat * Z))
  : list (nat * nat * Z) :=
  match ws with
  | [] => []
  | (w, a) :: rest =>
      let s := a + prev in
      let m := (next_w n rest / w)%nat in
      (w, m, s) :: shape_of n (Z.of_nat m * s) rest
  end.

(** [shape_of] is a right inverse of [coeffs]: the strides it builds
    give back exactly the coefficients it was handed. *)
Lemma coeffs_shape_of (n : nat) (ws : list (nat * Z)) (prev : Z) :
  coeffs prev (shape_of n prev ws) = ws.
Proof.
  revert prev. induction ws as [| [w a] ws IH]; intros prev; [reflexivity |].
  simpl. rewrite IH. f_equal. f_equal. ring.
Qed.

Lemma shape_of_nonnil (n : nat) (prev : Z) (ws : list (nat * Z)) :
  ws <> [] -> shape_of n prev ws <> [].
Proof.
  destruct ws as [| [w a] ws]; [contradiction | discriminate].
Qed.

(** Unfolding lemmas, so the proofs below can expose one entry at a
    time without [simpl] unfolding the recursive calls they need to
    keep folded. *)

Lemma shape_of_cons (n : nat) (prev : Z) (w : nat) (a : Z)
      (rest : list (nat * Z)) :
  shape_of n prev ((w, a) :: rest)
  = (w, (next_w n rest / w)%nat, a + prev)
    :: shape_of n (Z.of_nat (next_w n rest / w)%nat * (a + prev)) rest.
Proof. reflexivity. Qed.

(** The size of a shape is decided by its LAST entry. *)
Lemma nof_cons_cons (x y : nat * nat * Z) (T : list (nat * nat * Z)) :
  nof (x :: y :: T) = nof (y :: T).
Proof. destruct x as [[w m] s]. reflexivity. Qed.

Lemma tsize_cons (w m : nat) (s : Z) (T : list (nat * nat * Z)) :
  tsize ((w, m, s) :: T) = (m * tsize T)%nat.
Proof. reflexivity. Qed.

(** A positive number's divisor is at most it. *)
Lemma divide_le (w n : nat) : (1 <= n)%nat -> Nat.divide w n -> (w <= n)%nat.
Proof. intros Hn Hd. apply Nat.divide_pos_le; [lia | exact Hd]. Qed.

(** Exact division, in the form the shape construction needs. *)
Lemma divide_exact (w x : nat) :
  (w <> 0)%nat -> Nat.divide w x -> x = (w * (x / w))%nat.
Proof.
  intros Hw Hd. apply Nat.Div0.div_exact.
  apply Nat.Lcm0.mod_divide; assumption.
Qed.

(** The shape built from a chain is well formed: its weights are the
    chain's, and each is the previous one times its radix. *)
Lemma wf_shape_of (n : nat) :
  (1 <= n)%nat ->
  forall ws prev lo p,
    (1 <= lo)%nat -> chain_ok p lo n ws -> wf (shape_of n prev ws).
Proof.
  intros Hn ws. induction ws as [| [w a] ws IH]; intros prev lo p Hlo Hc.
  - exact I.
  - simpl in Hc. destruct Hc as [Hdp [Hdn [Hlow Hrest]]].
    assert (Hw1 : (1 <= w)%nat) by lia.
    (* the radix is the next weight over this one, and is positive *)
    assert (Hnext : (w <= next_w n ws)%nat).
    { destruct ws as [| [w' a'] ws']; simpl.
      - apply divide_le; assumption.
      - simpl in Hrest. destruct Hrest as [_ [_ [Hge _]]]. lia. }
    assert (Hdiv : Nat.divide w (next_w n ws)).
    { destruct ws as [| [w' a'] ws']; simpl; [exact Hdn |].
      simpl in Hrest. destruct Hrest as [Hd _]. exact Hd. }
    assert (Hm : (next_w n ws / w <> 0)%nat).
    { intro Hz.
      assert (next_w n ws = (w * (next_w n ws / w))%nat)
        by (apply divide_exact; [lia | exact Hdiv]).
      rewrite Hz, Nat.mul_0_r in *. lia. }
    simpl. split; [lia |]. split; [exact Hm |].
    destruct ws as [| [w' a'] ws'].
    + exact I.
    + simpl in Hrest. destruct Hrest as [Hd' [Hdn' [Hge' Hrest']]].
      split.
      * (* the next weight IS this weight times the radix *)
        simpl. apply divide_exact; [lia | exact Hd'].
      * apply (IH (Z.of_nat (next_w n ((w', a') :: ws') / w) * (a + prev))
                  (S w) w); [lia |].
        simpl. split; [exact Hd' |]. split; [exact Hdn' |].
        split; [lia | exact Hrest'].
Qed.

(** Its size is [n]: the top weight times the top radix. *)
Lemma nof_shape_of (n : nat) :
  (1 <= n)%nat ->
  forall ws prev lo p,
    ws <> [] -> (1 <= lo)%nat -> chain_ok p lo n ws ->
    nof (shape_of n prev ws) = n.
Proof.
  intros Hn ws. induction ws as [| [w a] ws IH]; intros prev lo p Hne Hlo Hc;
    [contradiction |].
  simpl in Hc. destruct Hc as [Hdp [Hdn [Hlow Hrest]]].
  rewrite shape_of_cons.
  destruct ws as [| [w' a'] ws'].
  - (* last entry: w * (n / w) = n because w divides n *)
    simpl. symmetry. apply divide_exact; [lia | exact Hdn].
  - (* not last: the size is the tail's *)
    rewrite shape_of_cons, nof_cons_cons, <- shape_of_cons.
    eapply (IH _ (S w) w); [discriminate | lia | exact Hrest].
Qed.

(** The head weight of a chain. *)
Definition hdw (ws : list (nat * Z)) : nat :=
  match ws with
  | [] => 1%nat
  | (w, _) :: _ => w
  end.

(** The product of the radices, against the head weight: the
    telescoping identity [w_1 * (n / w_1) = n]. *)
Lemma tsize_shape_of (n : nat) :
  (1 <= n)%nat ->
  forall ws prev lo p,
    ws <> [] -> (1 <= lo)%nat -> chain_ok p lo n ws ->
    (hdw ws * tsize (shape_of n prev ws))%nat = n.
Proof.
  intros Hn ws. induction ws as [| [w a] ws IH]; intros prev lo p Hne Hlo Hc;
    [contradiction |].
  simpl in Hc. destruct Hc as [Hdp [Hdn [Hlow Hrest]]].
  rewrite shape_of_cons.
  destruct ws as [| [w' a'] ws'].
  - (* one entry: the single radix is n / w *)
    simpl. rewrite Nat.mul_1_r. symmetry.
    apply divide_exact; [lia | exact Hdn].
  - (* the w' / w of this entry cancels the w' the tail contributes *)
    assert (Hrestc := Hrest).
    destruct Hrestc as [Hd' [Hdn' [Hge' Hrest']]].
    assert (Hw1 : (1 <= w)%nat) by lia.
    assert (IHtail : (w' * tsize (shape_of n
              (Z.of_nat (next_w n ((w', a') :: ws') / w)%nat * (a + prev))
              ((w', a') :: ws')))%nat = n)
      by (apply (IH _ (S w) w); [discriminate | lia | exact Hrest]).
    rewrite tsize_cons.
    change (hdw ((w, a) :: (w', a') :: ws')) with w.
    change (next_w n ((w', a') :: ws')) with w'.
    rewrite Nat.mul_assoc.
    replace (w * (w' / w))%nat with w'
      by (apply divide_exact; [lia | exact Hd']).
    exact IHtail.
Qed.

(** Weight [1] is a boundary of every refinement --- its digits must
    cover the axis --- so the chain carries it whatever its
    coefficient. Without it the radices would multiply to [n / w_1]
    rather than [n]: for [g v = v / 2] on [n = 4] the scan reports only
    weight [2], and the shape is [(2, 2)] with strides [(0, 1)]. This
    mirrors [boundaries = ref [ 1 ]] in the OCaml [Decide.fit_axis]. *)
Definition with_one (ws : list (nat * Z)) : list (nat * Z) :=
  match ws with
  | [] => [(1%nat, 0)]
  | (w, _) :: _ => if Nat.eqb w 1 then ws else (1%nat, 0) :: ws
  end.

Lemma hdw_with_one (ws : list (nat * Z)) : hdw (with_one ws) = 1%nat.
Proof.
  destruct ws as [| [w a] ws]; [reflexivity |].
  simpl. destruct (Nat.eqb_spec w 1) as [-> | Hne]; reflexivity.
Qed.

Lemma with_one_nonnil (ws : list (nat * Z)) : with_one ws <> [].
Proof.
  destruct ws as [| [w a] ws]; [discriminate |].
  simpl. destruct (Nat.eqb w 1); discriminate.
Qed.

(** A zero coefficient at weight 1 changes no value. *)
Lemma fsum_with_one (ws : list (nat * Z)) (v : nat) :
  fsum (with_one ws) v = fsum ws v.
Proof.
  destruct ws as [| [w a] ws]; [simpl; ring |].
  simpl. destruct (Nat.eqb w 1); [reflexivity | simpl; ring].
Qed.

Lemma chain_ok_with_one (n : nat) (ws : list (nat * Z)) :
  (1 <= n)%nat -> chain_ok 1%nat 1%nat n ws ->
  chain_ok 1%nat 1%nat n (with_one ws).
Proof.
  intros Hn Hc. destruct ws as [| [w a] ws].
  - simpl.
    split; [apply Nat.divide_1_l |].
    split; [apply Nat.divide_1_l |].
    split; [lia | exact I].
  - simpl. destruct (Nat.eqb_spec w 1) as [-> | Hne]; simpl.
    + exact Hc.
    + (* the first weight is at least 2, so 1 sits strictly below it *)
      assert (Hcc := Hc). simpl in Hcc. destruct Hcc as [H1 [H2 [H3 H4]]].
      split; [apply Nat.divide_1_l |].
      split; [apply Nat.divide_1_l |].
      split; [lia |].
      split; [exact H1 |].
      split; [exact H2 |].
      split; [lia | exact H4].
Qed.

(** The shape for a chain: the chain with weight [1] forced in. *)
Definition shape_of_chain (n : nat) (ws : list (nat * Z))
  : list (nat * nat * Z) :=
  shape_of n 0 (with_one ws).

(** The paper's Theorem 1, accepting direction, as a statement about
    LAYOUTS: if the scan accepts, [g] is the index function of a flat
    shape whose radices multiply to [n]. *)
Theorem scan_sound_layout (n : nat) (g : nat -> Z) (ws : list (nat * Z)) :
  (1 <= n)%nat -> g 0%nat = 0 -> scan n g = Some ws ->
  let T := shape_of_chain n ws in
  wf T /\ tsize T = n /\ nof T = n
  /\ forall v, (v < n)%nat -> g v = dgsum T v.
Proof.
  intros Hn Hg0 Hscan.
  destruct (scan_sound n g ws Hn Hg0 Hscan) as [Hch HR].
  assert (Hch1 : chain_ok 1%nat 1%nat n (with_one ws))
    by (apply chain_ok_with_one; assumption).
  cbv zeta. unfold shape_of_chain.
  assert (Hwf : wf (shape_of n 0 (with_one ws)))
    by (eapply (wf_shape_of n Hn _ 0 1%nat 1%nat); [lia | exact Hch1]).
  assert (Hnof : nof (shape_of n 0 (with_one ws)) = n)
    by (eapply (nof_shape_of n Hn _ 0 1%nat 1%nat);
        [apply with_one_nonnil | lia | exact Hch1]).
  assert (Htsz : tsize (shape_of n 0 (with_one ws)) = n).
  { pose proof (tsize_shape_of n Hn (with_one ws) 0 1%nat 1%nat
                  (with_one_nonnil ws) (Nat.le_refl 1) Hch1) as Ht.
    rewrite hdw_with_one in Ht. lia. }
  split; [exact Hwf |]. split; [exact Htsz |]. split; [exact Hnof |].
  intros v Hv.
  rewrite (dgsum_is_fsum _ v Hwf) by (rewrite Hnof; exact Hv).
  rewrite coeffs_shape_of, fsum_with_one.
  exact (HR v Hv).
Qed.
