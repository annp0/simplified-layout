(** * Completeness of the scan

    The other direction of the paper's Theorem 1: if [g] IS a floor
    form over some chain, the scan accepts it.

    The argument needs only one invariant, and a weaker one than the
    paper's: at step [t], the chain still to be found accounts for
    exactly the part of the first difference that the committed list
    does not. Then

      residual at t = (what the remaining chain contributes at t)

    and since every remaining weight is at least [t], and a weight
    above [t] cannot divide [t], that contribution is the coefficient
    of [t] if [t] is the next weight and zero otherwise. So the scan
    commits precisely at the weights of the given chain, in order, and
    its two divisibility checks are exactly the chain conditions --- it
    cannot reject. *)

From Coq Require Import Arith Lia ZArith List Bool.
From LayoutAlgebra Require Import Floors Chain Recognize.
Import ListNotations.

Open Scope Z_scope.

(** ** The scan with its state exposed

    [scan_from] returns only the committed list. The same recursion
    returning [(t, wlast, acc)] is what the induction below needs. *)
Fixpoint run (n : nat) (h : nat -> Z) (steps t wlast : nat)
             (acc : list (nat * Z)) : option (nat * nat * list (nat * Z)) :=
  match steps with
  | 0%nat => Some (t, wlast, acc)
  | S steps' =>
      let r := resid h acc t in
      if Z.eqb r 0
      then run n h steps' (S t) wlast acc
      else if andb (Nat.eqb (n mod t) 0) (Nat.eqb (t mod wlast) 0)
           then run n h steps' (S t) t (acc ++ [(t, r)])
           else None
  end.

Lemma scan_from_run (steps n : nat) (h : nat -> Z) :
  forall t wlast acc,
    scan_from n h steps t wlast acc
    = option_map (fun st => snd st) (run n h steps t wlast acc).
Proof.
  induction steps as [| steps IH]; intros t wlast acc; [reflexivity |].
  simpl. destruct (Z.eqb (resid h acc t) 0); [apply IH |].
  destruct (andb (Nat.eqb (n mod t) 0) (Nat.eqb (t mod wlast) 0));
    [apply IH | reflexivity].
Qed.

(** ** Chains: weights are bounded below, and zero coefficients drop out *)

Lemma chain_ok_weights_ge (prev lo n : nat) (ws : list (nat * Z)) :
  chain_ok prev lo n ws -> Forall (fun p => (lo <= fst p)%nat) ws.
Proof.
  revert prev lo. induction ws as [| [w a] ws IH]; intros prev lo Hc;
    [constructor |].
  simpl in Hc. destruct Hc as [H1 [H2 [H3 H4]]].
  constructor; simpl; [lia |].
  eapply Forall_impl; [| apply (IH w (S w) H4)]. simpl. lia.
Qed.

(** Weakening the predecessor along divisibility: only the head of a
    chain mentions it, and divisibility is transitive. *)
Lemma chain_ok_prev_weaken (prev prev' lo n : nat) (ws : list (nat * Z)) :
  Nat.divide prev' prev -> chain_ok prev lo n ws -> chain_ok prev' lo n ws.
Proof.
  intros Hd. destruct ws as [| [w a] ws]; [easy |].
  simpl. intros [H1 [H2 [H3 H4]]].
  repeat split; try assumption.
  eapply Nat.divide_trans; [exact Hd | exact H1].
Qed.

(** Entries with a zero coefficient contribute nothing, and dropping
    them leaves a chain --- divisibility bridges the gap. *)
Definition nzs (ws : list (nat * Z)) : list (nat * Z) :=
  filter (fun p => negb (Z.eqb (snd p) 0)) ws.

Lemma dsum_nzs (ws : list (nat * Z)) (t : nat) : dsum (nzs ws) t = dsum ws t.
Proof.
  induction ws as [| [w a] ws IH]; [reflexivity |].
  simpl. destruct (Z.eqb_spec a 0) as [-> | Hne]; simpl.
  - rewrite IH. ring.
  - rewrite IH. ring.
Qed.

Lemma nzs_nonzero (ws : list (nat * Z)) :
  Forall (fun p => snd p <> 0) (nzs ws).
Proof.
  induction ws as [| [w a] ws IH]; [constructor |].
  simpl. destruct (Z.eqb_spec a 0) as [-> | Hne]; [exact IH |].
  constructor; [simpl; exact Hne | exact IH].
Qed.

Lemma chain_ok_nzs (n : nat) :
  forall ws prev lo, chain_ok prev lo n ws -> chain_ok prev lo n (nzs ws).
Proof.
  induction ws as [| [w a] ws IH]; intros prev lo Hc; [exact I |].
  simpl in Hc. destruct Hc as [H1 [H2 [H3 H4]]].
  simpl. destruct (Z.eqb_spec a 0) as [-> | Hne]; simpl.
  - (* dropped: bridge prev past w, and relax the lower bound *)
    eapply chain_ok_prev_weaken; [exact H1 |].
    eapply chain_ok_lo_mono; [| apply (IH w (S w) H4)]. lia.
  - repeat split; try assumption. apply (IH w (S w) H4).
Qed.

(** ** The scan cannot reject *)

Lemma run_complete :
  forall steps n h t wlast acc ws,
    (1 <= t)%nat -> (1 <= wlast)%nat -> (t + steps <= n)%nat ->
    (forall t', (1 <= t')%nat -> (t' < n)%nat ->
       h t' = dsum (acc ++ ws) t') ->
    chain_ok wlast t n ws ->
    Forall (fun p => snd p <> 0) ws ->
    exists st, run n h steps t wlast acc = Some st.
Proof.
  induction steps as [| steps IH];
    intros n h t wlast acc ws Ht Hwlast Hsteps Hrep Hch Hnz.
  - exists (t, wlast, acc). reflexivity.
  - (* the residual at t is what the remaining chain contributes there *)
    assert (Htn : (t < n)%nat) by lia.
    assert (Hres : resid h acc t = dsum ws t).
    { unfold resid. rewrite (Hrep t Ht Htn), dsum_app. ring. }
    destruct ws as [| [w a] ws'].
    + (* nothing left to find: every later residual is zero *)
      simpl in Hres.
      simpl. rewrite Hres. simpl.
      apply (IH n h (S t) wlast acc []);
        [lia | lia | lia | exact Hrep | exact I | constructor].
    + simpl in Hch. destruct Hch as [Hdw [Hdn [Hlow Hch']]].
      assert (Hge' : Forall (fun p => (S w <= fst p)%nat) ws')
        by (apply (chain_ok_weights_ge w (S w) n); exact Hch').
      destruct (Nat.eq_dec w t) as [-> | Hne].
      * (* t IS the next weight: commit, and both checks hold *)
        assert (Hrest0 : dsum ws' t = 0).
        { apply dsum_above; [lia |].
          eapply Forall_impl; [| exact Hge']. simpl. lia. }
        assert (Hresa : resid h acc t = a).
        { rewrite Hres. simpl.
          rewrite divides_ind_self by lia. rewrite Hrest0. ring. }
        assert (Hane : a <> 0) by (inversion Hnz as [| ? ? Hh ?]; exact Hh).
        simpl. rewrite Hresa.
        destruct (Z.eqb_spec a 0) as [Heq0 | _]; [contradiction |].
        (* n mod t = 0 and t mod wlast = 0 *)
        assert (Hmn : (n mod t = 0)%nat)
          by (apply Nat.Lcm0.mod_divide; exact Hdn).
        assert (Hmw : (t mod wlast = 0)%nat)
          by (apply Nat.Lcm0.mod_divide; exact Hdw).
        rewrite Hmn, Hmw. simpl.
        rewrite <- Hresa.
        apply (IH n h (S t) t (acc ++ [(t, resid h acc t)]) ws');
          [lia | lia | lia | | exact Hch' | inversion Hnz; assumption].
        intros t' H1 H2. rewrite <- app_assoc. rewrite Hresa. now apply Hrep.
      * (* t is not the next weight: nothing divides t, residual zero *)
        assert (Hzero : dsum ((w, a) :: ws') t = 0).
        { apply dsum_above; [lia |].
          constructor; simpl; [lia |].
          eapply Forall_impl; [| exact Hge']. simpl. lia. }
        simpl. rewrite Hres, Hzero. simpl.
        apply (IH n h (S t) wlast acc ((w, a) :: ws'));
          [lia | lia | lia | | | exact Hnz].
        -- intros t' H1 H2. now apply Hrep.
        -- simpl. repeat split; try assumption. lia.
Qed.

(** The paper's Theorem 1, accepting side of the "if and only if": a
    map that is a floor form over some chain of divisors of [n] is
    accepted by the scan. *)
Theorem scan_complete (n : nat) (g : nat -> Z) (ws : list (nat * Z)) :
  (1 <= n)%nat -> g 0%nat = 0 ->
  chain_ok 1%nat 1%nat n ws -> Represents n g ws ->
  exists ws', scan n g = Some ws'.
Proof.
  intros Hn Hg0 Hch HR.
  assert (Hpos : weights_pos ws)
    by (eapply chain_ok_weights_pos; [apply Nat.le_refl | exact Hch]).
  assert (Hdiff : forall t, (1 <= t)%nat -> (t < n)%nat ->
            first_diff g t = dsum ws t).
  { intros t H1 H2. unfold first_diff.
    apply (proj1 (represents_iff n g ws Hg0 Hpos) HR t H1 H2). }
  unfold scan. rewrite scan_from_run.
  destruct (run_complete (n - 1)%nat n (first_diff g) 1%nat 1%nat [] (nzs ws))
    as [st Hst];
    [lia | lia | lia | | apply chain_ok_nzs; exact Hch | apply nzs_nonzero |].
  - intros t' H1 H2. simpl. rewrite dsum_nzs. now apply Hdiff.
  - rewrite Hst. exists (snd st). reflexivity.
Qed.

(** ** Theorem 1, as an "if and only if"

    Combining with [Recognize.scan_sound]: the scan accepts exactly
    the maps that are floor forms over a chain of divisors of [n] ---
    equivalently (via [Shape.scan_sound_layout]) exactly the maps that
    are index functions of a flat shape of size [n]. *)
Theorem scan_iff (n : nat) (g : nat -> Z) :
  (1 <= n)%nat -> g 0%nat = 0 ->
  (exists ws, chain_ok 1%nat 1%nat n ws /\ Represents n g ws)
  <-> (exists ws', scan n g = Some ws').
Proof.
  intros Hn Hg0. split.
  - intros [ws [Hch HR]]. eapply scan_complete; eassumption.
  - intros [ws' Hscan]. exists ws'. now apply scan_sound.
Qed.
