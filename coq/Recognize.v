(** * The scan, and its soundness

    The scan of the paper's Theorem 1. It walks [t = 1, ..., n-1] and
    keeps the weights it has already committed to. At each [t] the
    RESIDUAL is the first difference of [g] at [t] minus what the
    committed weights already contribute there; by
    [Chain.fsum_step] a weight contributes exactly at its own
    multiples, so a nonzero residual forces [t] to be a weight and
    forces its coefficient to be that residual.

    The paper phrases this as mutating a copy of the first difference.
    Here the residual is recomputed from the committed list instead,
    which is the same number --- the paper's own invariant --- and
    avoids modelling the mutation.

    This file proves SOUNDNESS: if the scan accepts, the list it
    returns is a chain of divisors of [n] and [g] really is that
    floor form on [[0, n)]. *)

From Coq Require Import Arith Lia ZArith List.
From LayoutAlgebra Require Import Floors Chain.
Import ListNotations.

Open Scope Z_scope.

(** ** Indicator sums over lists *)

Lemma dsum_app (a b : list (nat * Z)) (t : nat) :
  dsum (a ++ b) t = dsum a t + dsum b t.
Proof.
  induction a as [| p a IH]; simpl; [ring | rewrite IH; ring].
Qed.

Lemma divides_ind_above (w t : nat) :
  (1 <= t)%nat -> (t < w)%nat -> divides_ind w t = 0.
Proof.
  intros Ht Hw. apply divides_ind_false.
  rewrite Nat.mod_small by lia. lia.
Qed.

Lemma divides_ind_self (t : nat) : (1 <= t)%nat -> divides_ind t t = 1.
Proof.
  intros Ht. apply divides_ind_true. now apply Nat.Div0.mod_same.
Qed.

(** Weights strictly above [t] contribute nothing at [t]. This is what
    makes the scan's committed list final: whatever it commits later
    cannot disturb what it has already settled. *)
Lemma dsum_above (ws : list (nat * Z)) (t : nat) :
  (1 <= t)%nat -> Forall (fun p => (t < fst p)%nat) ws -> dsum ws t = 0.
Proof.
  intros Ht. induction ws as [| p ws IH]; [reflexivity |].
  intros H. inversion H as [| ? ? Hp Hrest]; subst. simpl.
  rewrite divides_ind_above by assumption.
  rewrite IH by assumption. ring.
Qed.

(** ** Chains *)

(** [chain_ok prev lo n ws]: the weights of [ws] are at least [lo],
    strictly increasing, each divides [n], and each is divisible by the
    one before ([prev] for the first). This is the paper's
    [1 = w_1 | w_2 | ... | w_k | n]. *)
Fixpoint chain_ok (prev lo n : nat) (ws : list (nat * Z)) : Prop :=
  match ws with
  | [] => True
  | (w, _) :: rest =>
      Nat.divide prev w /\ Nat.divide w n /\ (lo <= w)%nat
      /\ chain_ok w (S w) n rest
  end.

Lemma chain_ok_lo_mono (prev lo lo' n : nat) (ws : list (nat * Z)) :
  (lo' <= lo)%nat -> chain_ok prev lo n ws -> chain_ok prev lo' n ws.
Proof.
  intros Hle. destruct ws as [| [w a] ws]; [easy |].
  simpl. intros [H1 [H2 [H3 H4]]]. repeat split; try assumption. lia.
Qed.

Lemma chain_ok_weights_pos (prev lo n : nat) (ws : list (nat * Z)) :
  (1 <= lo)%nat -> chain_ok prev lo n ws -> weights_pos ws.
Proof.
  revert prev lo. induction ws as [| [w a] ws IH]; intros prev lo Hlo Hc.
  - constructor.
  - simpl in Hc. destruct Hc as [H1 [H2 [H3 H4]]].
    constructor; simpl; [lia |].
    apply (IH w (S w)); [lia | assumption].
Qed.

(** ** The scan *)

Definition resid (h : nat -> Z) (acc : list (nat * Z)) (t : nat) : Z :=
  h t - dsum acc t.

(** [steps] counts down the remaining values of [t]; [wlast] is the
    last weight committed (or [1]); [acc] is the committed list, in
    increasing order of weight. *)
Fixpoint scan_from (n : nat) (h : nat -> Z) (steps t wlast : nat)
                   (acc : list (nat * Z)) : option (list (nat * Z)) :=
  match steps with
  | 0%nat => Some acc
  | S steps' =>
      let r := resid h acc t in
      if Z.eqb r 0
      then scan_from n h steps' (S t) wlast acc
      else if andb (Nat.eqb (n mod t) 0) (Nat.eqb (t mod wlast) 0)
           then scan_from n h steps' (S t) t (acc ++ [(t, r)])
           else None
  end.

Definition first_diff (g : nat -> Z) (t : nat) : Z := g t - g (t - 1)%nat.

Definition scan (n : nat) (g : nat -> Z) : option (list (nat * Z)) :=
  scan_from n (first_diff g) (n - 1)%nat 1%nat 1%nat [].

(** ** Soundness of the scan *)

Lemma scan_from_sound :
  forall steps n h t wlast acc ws,
    (1 <= t)%nat -> (1 <= wlast)%nat ->
    Forall (fun p => (fst p < t)%nat) acc ->
    scan_from n h steps t wlast acc = Some ws ->
    exists extra,
      ws = acc ++ extra
      /\ Forall (fun p => (t <= fst p)%nat) extra
      /\ chain_ok wlast t n extra
      /\ (forall t', (t <= t')%nat -> (t' < t + steps)%nat -> h t' = dsum ws t').
Proof.
  induction steps as [| steps IH];
    intros n h t wlast acc ws Ht Hwlast Hacc Hscan.
  - (* no steps left: nothing more is committed *)
    simpl in Hscan. injection Hscan as <-.
    exists []. rewrite app_nil_r.
    split; [reflexivity |].
    split; [apply Forall_nil |].
    split; [exact I |].
    intros t' H1 H2. lia.
  - simpl in Hscan.
    destruct (Z.eqb_spec (resid h acc t) 0) as [Hr | Hr].
    + (* residual zero: commit nothing, move on *)
      assert (HaccS : Forall (fun p => (fst p < S t)%nat) acc).
      { eapply Forall_impl; [| exact Hacc]. simpl. lia. }
      destruct (IH n h (S t) wlast acc ws) as [extra [Hws [Hge [Hch Hval]]]];
        [lia | lia | exact HaccS | exact Hscan |].
      exists extra.
      split; [exact Hws |]. split; [| split].
      * eapply Forall_impl; [| exact Hge]. simpl. lia.
      * eapply chain_ok_lo_mono; [| exact Hch]. lia.
      * intros t' H1 H2.
        destruct (Nat.eq_dec t' t) as [-> | Hne].
        -- unfold resid in Hr.
           rewrite Hws, dsum_app.
           rewrite (dsum_above extra t) by
             (assumption || (eapply Forall_impl; [| exact Hge]; simpl; lia)).
           lia.
        -- apply Hval; lia.
    + (* residual nonzero: t must be a weight *)
      destruct (andb (Nat.eqb (n mod t) 0) (Nat.eqb (t mod wlast) 0)) eqn:Hchk;
        [| discriminate].
      apply andb_prop in Hchk. destruct Hchk as [Hn Hw].
      apply Nat.eqb_eq in Hn. apply Nat.eqb_eq in Hw.
      assert (Hdn : Nat.divide t n) by (apply Nat.mod_divide; [lia | exact Hn]).
      assert (Hdw : Nat.divide wlast t) by (apply Nat.mod_divide; [lia | exact Hw]).
      assert (HaccS : Forall (fun p => (fst p < S t)%nat) (acc ++ [(t, resid h acc t)])).
      { apply Forall_app. split.
        - eapply Forall_impl; [| exact Hacc]. simpl. lia.
        - constructor; simpl; [lia | apply Forall_nil]. }
      destruct (IH n h (S t) t (acc ++ [(t, resid h acc t)]) ws)
        as [extra [Hws [Hge [Hch Hval]]]]; [lia | lia | exact HaccS | exact Hscan |].
      exists ((t, resid h acc t) :: extra).
      split; [rewrite Hws, <- app_assoc; reflexivity |]. split; [| split].
      * constructor; simpl; [lia |].
        eapply Forall_impl; [| exact Hge]. simpl. lia.
      * simpl.
        split; [exact Hdw |]. split; [exact Hdn |]. split; [lia |].
        eapply chain_ok_lo_mono; [| exact Hch]. lia.
      * intros t' H1 H2.
        destruct (Nat.eq_dec t' t) as [-> | Hne].
        -- (* the committed coefficient is exactly the residual *)
           rewrite Hws, dsum_app, dsum_app.
           rewrite (dsum_above extra t) by
             (assumption || (eapply Forall_impl; [| exact Hge]; simpl; lia)).
           simpl. rewrite divides_ind_self by assumption.
           unfold resid. ring.
        -- apply Hval; lia.
Qed.

(** The paper's Theorem 1, accepting direction: if the scan accepts,
    its output is a chain of divisors of [n] and [g] is that floor form
    on the whole box. *)
Theorem scan_sound (n : nat) (g : nat -> Z) (ws : list (nat * Z)) :
  (1 <= n)%nat -> g 0%nat = 0 -> scan n g = Some ws ->
  chain_ok 1%nat 1%nat n ws /\ Represents n g ws.
Proof.
  intros Hn Hg0 Hscan. unfold scan in Hscan.
  destruct (scan_from_sound (n - 1)%nat n (first_diff g) 1%nat 1%nat [] ws)
    as [extra [Hws [_ [Hch Hval]]]]; [lia | lia | constructor | exact Hscan |].
  simpl in Hws. subst ws.
  split; [exact Hch |].
  apply (represents_iff n g extra Hg0
           (chain_ok_weights_pos 1%nat 1%nat n extra (Nat.le_refl 1) Hch)).
  intros t Ht1 Htn. apply Hval; lia.
Qed.
