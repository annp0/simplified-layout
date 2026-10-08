(** * The scan as the paper runs it, and its cost

    [Recognize.scan] recomputes the residual at each [t] from the
    committed list. The paper (and [Decide.fit_axis]) instead keeps a
    copy [rho] of the first difference and, on committing [t] with
    coefficient [a], subtracts [a] from [rho] at every multiple of [t]
    in [[t, n)]. This file writes that algorithm down, with [rho] an
    array updated one entry at a time and a counter beside it, and
    proves

    - it returns exactly what [Recognize.scan] returns ([fscan_eq]),
      so every theorem about [scan] holds of it;
    - it performs at most [3 (n - 1)] operations on [rho]
      ([fscan_linear]): one read per [t], and one write per multiple
      touched by a subtraction --- fewer than [2 (n - 1)] in all,
      because each committed weight is at least twice the one before.

    The counter is the paper's cost model. It does not count the
    committed list, which has at most [log2 n] entries. *)

From Stdlib Require Import Arith Lia ZArith List Bool.
From LayoutAlgebra Require Import Floors Chain Recognize.
Import ListNotations.

Open Scope Z_scope.

(** ** The subtraction loop *)

(** One array write. *)
Definition upd (rho : nat -> Z) (i : nat) (z : Z) : nat -> Z :=
  fun j => if Nat.eqb j i then z else rho j.

(** [rho(t) -= a] for [t = t0, t0 + w, t0 + 2w, ...] below [n], with the
    number of writes. [fuel] only bounds the recursion; [n] suffices. *)
Fixpoint sub_mult (n w : nat) (a : Z) (fuel t : nat) (rho : nat -> Z)
  : (nat -> Z) * nat :=
  match fuel with
  | 0%nat => (rho, 0%nat)
  | S fuel' =>
      if Nat.ltb t n
      then let '(rho', c) := sub_mult n w a fuel' (t + w) (upd rho t (rho t - a)) in
           (rho', S c)
      else (rho, 0%nat)
  end.

(** Started at a multiple of [w], the loop subtracts [a] at exactly the
    multiples of [w] in [[t, n)]. *)
Lemma sub_mult_spec (n w : nat) (a : Z) :
  (1 <= w)%nat ->
  forall fuel t rho, Nat.divide w t -> (n <= t + fuel)%nat ->
  forall x, fst (sub_mult n w a fuel t rho) x
            = if andb (Nat.leb t x) (Nat.ltb x n)
              then rho x - a * divides_ind w x else rho x.
Proof.
  intros Hw fuel. induction fuel as [| fuel IH]; intros t rho [q Hq] Hfuel x.
  - simpl. destruct (Nat.leb_spec t x); destruct (Nat.ltb_spec x n);
      simpl; try reflexivity; lia.
  - simpl. destruct (Nat.ltb_spec t n) as [Htn | Htn].
    + destruct (sub_mult n w a fuel (t + w) (upd rho t (rho t - a)))
        as [rho' c] eqn:E.
      simpl.
      assert (Hdiv : Nat.divide w (t + w)) by (exists (S q); lia).
      pose proof (IH (t + w)%nat (upd rho t (rho t - a)) Hdiv ltac:(lia) x) as H.
      rewrite E in H. simpl in H. rewrite H. unfold upd.
      destruct (Nat.eqb_spec x t) as [-> | Hne].
      * (* the entry written now *)
        rewrite (divides_ind_true w t) by (subst t; apply Nat.Div0.mod_mul).
        destruct (Nat.leb_spec (t + w) t); [lia |].
        destruct (Nat.leb_spec t t); [| lia].
        destruct (Nat.ltb_spec t n); [| lia]. simpl. ring.
      * destruct (Nat.leb_spec (t + w) x) as [Hge | Hlt].
        -- (* a later entry: the recursion handles it *)
           destruct (Nat.leb_spec t x); [| lia]. reflexivity.
        -- destruct (Nat.leb_spec t x) as [Htx | Htx]; simpl;
             [| reflexivity].
           destruct (Nat.ltb_spec x n); simpl; [| reflexivity].
           (* strictly between two multiples of w: not a multiple *)
           rewrite (divides_ind_false w x); [ring |].
           intros Hm. apply Nat.Div0.mod_divides in Hm. destruct Hm as [p Hp].
           subst t x. destruct (Nat.le_gt_cases p q) as [Hpq | Hpq].
           ++ assert (w * p <= w * q)%nat by (apply Nat.mul_le_mono_l; exact Hpq).
              lia.
           ++ assert (w * (q + 1) <= w * p)%nat by (apply Nat.mul_le_mono_l; lia).
              lia.
    + simpl. destruct (Nat.leb_spec t x); destruct (Nat.ltb_spec x n);
        simpl; try reflexivity; lia.
Qed.

(** Each write moves [t] up by [w] and stops at [n]: the writes number
    at most [(n + w - 1 - t) / w]. *)
Lemma sub_mult_cost (n w : nat) (a : Z) :
  (1 <= w)%nat ->
  forall fuel t rho, (snd (sub_mult n w a fuel t rho) * w <= n + w - 1 - t)%nat.
Proof.
  intros Hw fuel. induction fuel as [| fuel IH]; intros t rho; simpl; [lia |].
  destruct (Nat.ltb_spec t n) as [Htn | Htn]; [| simpl; lia].
  destruct (sub_mult n w a fuel (t + w) (upd rho t (rho t - a))) as [rho' c] eqn:E.
  pose proof (IH (t + w)%nat (upd rho t (rho t - a))) as H.
  rewrite E in H. simpl in H |- *. lia.
Qed.

(** ** The scan with [rho] *)

(** As [Recognize.scan_from], but reading [rho] where that recomputes
    the residual, and subtracting on commit. The committed list is
    built in reverse; the second component counts operations on [rho]. *)
Fixpoint fscan_from (n : nat) (rho : nat -> Z) (steps t wlast : nat)
                    (acc : list (nat * Z)) : option (list (nat * Z)) * nat :=
  match steps with
  | 0%nat => (Some (rev acc), 0%nat)
  | S steps' =>
      let r := rho t in
      if Z.eqb r 0
      then let '(res, c) := fscan_from n rho steps' (S t) wlast acc in
           (res, S c)
      else if andb (Nat.eqb (n mod t) 0) (Nat.eqb (t mod wlast) 0)
           then let '(rho', c1) := sub_mult n t r n t rho in
                let '(res, c2) := fscan_from n rho' steps' (S t) t ((t, r) :: acc) in
                (res, S (c1 + c2))
           else (None, 1%nat)
  end.

Definition fscan_run (n : nat) (g : nat -> Z) : option (list (nat * Z)) * nat :=
  fscan_from n (first_diff g) (n - 1)%nat 1%nat 1%nat [].

Definition fscan (n : nat) (g : nat -> Z) : option (list (nat * Z)) :=
  fst (fscan_run n g).

Definition fscan_cost (n : nat) (g : nat -> Z) : nat :=
  snd (fscan_run n g).

(** ** Same answer as [Recognize.scan] *)

(** The paper's invariant: [rho] holds the residual. *)
Lemma fscan_from_eq (n : nat) (h : nat -> Z) :
  forall steps rho t wlast acc,
    (1 <= t)%nat -> (t + steps <= n)%nat ->
    (forall x, (1 <= x)%nat -> (x < n)%nat -> rho x = h x - dsum (rev acc) x) ->
    fst (fscan_from n rho steps t wlast acc) = scan_from n h steps t wlast (rev acc).
Proof.
  intros steps. induction steps as [| steps IH];
    intros rho t wlast acc Ht Hsteps Hinv; [reflexivity |].
  simpl. unfold resid. rewrite <- (Hinv t) by lia.
  destruct (Z.eqb_spec (rho t) 0) as [Hr | Hr].
  - destruct (fscan_from n rho steps (S t) wlast acc) as [res c] eqn:E.
    simpl. rewrite <- (IH rho (S t) wlast acc) by (lia || exact Hinv).
    now rewrite E.
  - destruct (andb (Nat.eqb (n mod t) 0) (Nat.eqb (t mod wlast) 0)); [| reflexivity].
    destruct (sub_mult n t (rho t) n t rho) as [rho' c1] eqn:Es.
    destruct (fscan_from n rho' steps (S t) t ((t, rho t) :: acc)) as [res c2] eqn:E.
    simpl.
    assert (Hinv' : forall x, (1 <= x)%nat -> (x < n)%nat ->
              rho' x = h x - dsum (rev ((t, rho t) :: acc)) x).
    { intros x Hx1 Hxn.
      pose proof (sub_mult_spec n t (rho t) Ht n t rho
                    (Nat.divide_refl t) ltac:(lia) x) as Hs.
      rewrite Es in Hs. simpl in Hs. rewrite Hs.
      simpl rev. rewrite dsum_app. simpl.
      destruct (Nat.leb_spec t x); destruct (Nat.ltb_spec x n); simpl; try lia.
      - rewrite (Hinv x) by assumption. ring.
      - rewrite (Hinv x) by assumption.
        rewrite (divides_ind_above t x) by lia. ring. }
    pose proof (IH rho' (S t) t ((t, rho t) :: acc) ltac:(lia) ltac:(lia) Hinv') as H.
    rewrite E in H. cbn [rev fst] in H. exact H.
Qed.

Theorem fscan_eq (n : nat) (g : nat -> Z) :
  (1 <= n)%nat -> fscan n g = scan n g.
Proof.
  intros Hn. unfold fscan, fscan_run, scan.
  apply (fscan_from_eq n (first_diff g) (n - 1)%nat (first_diff g) 1%nat 1%nat []);
    [lia | lia |].
  intros x _ _. simpl. ring.
Qed.

(** ** At most [3 (n - 1)] operations *)

Lemma div_of_mul_le (c t N : nat) : (1 <= t)%nat -> (c * t <= N)%nat -> (c <= N / t)%nat.
Proof.
  intros Ht H. apply Nat.div_le_lower_bound; lia.
Qed.

(** Halving the budget: [2 * (N / 2t) <= N / t]. *)
Lemma div_double (N t : nat) : (1 <= t)%nat -> (2 * (N / (2 * t)) <= N / t)%nat.
Proof.
  intros Ht. apply Nat.div_le_lower_bound; [lia |].
  pose proof (Nat.Div0.mul_div_le N (2 * t)). lia.
Qed.

(** [L] is a lower bound on every weight the scan can still commit.
    From [t] on, a weight is at least [t] and a multiple of [wlast];
    once [t] is committed the next weight is a proper multiple of it,
    so at least [2t]. The budget [2 (N / L)] therefore halves with
    each commit while the commit itself spends at most [N / t]. *)
Lemma fscan_from_cost (n : nat) :
  forall steps rho t wlast acc L,
    (1 <= L)%nat -> (1 <= t)%nat ->
    (forall w, (t <= w)%nat -> Nat.divide wlast w -> (L <= w)%nat) ->
    (snd (fscan_from n rho steps t wlast acc) <= steps + 2 * ((n - 1) / L))%nat.
Proof.
  intros steps. induction steps as [| steps IH];
    intros rho t wlast acc L HL Ht Hlow; simpl; [lia |].
  destruct (Z.eqb (rho t) 0).
  - destruct (fscan_from n rho steps (S t) wlast acc) as [res c] eqn:E.
    pose proof (IH rho (S t) wlast acc L HL ltac:(lia)
                  ltac:(intros w Hw Hd; apply Hlow; [lia | exact Hd])) as H.
    rewrite E in H. simpl in H |- *. lia.
  - destruct (andb (Nat.eqb (n mod t) 0) (Nat.eqb (t mod wlast) 0)) eqn:Hchk;
      [| simpl; lia].
    apply andb_prop in Hchk. destruct Hchk as [_ Hw].
    apply Nat.eqb_eq in Hw.
    assert (HLt : (L <= t)%nat).
    { apply Hlow; [lia |].
      apply Nat.Div0.mod_divides in Hw. destruct Hw as [q Hq].
      exists q. lia. }
    destruct (sub_mult n t (rho t) n t rho) as [rho' c1] eqn:Es.
    destruct (fscan_from n rho' steps (S t) t ((t, rho t) :: acc)) as [res c2] eqn:E.
    simpl.
    (* the subtraction: at most N / t writes *)
    pose proof (sub_mult_cost n t (rho t) Ht n t rho) as Hc1.
    rewrite Es in Hc1. simpl in Hc1.
    assert (Hc1' : (c1 <= (n - 1) / t)%nat) by (apply div_of_mul_le; lia).
    (* the rest: weights are now proper multiples of t *)
    pose proof (IH rho' (S t) t ((t, rho t) :: acc) (2 * t)%nat ltac:(lia) ltac:(lia)
                  ltac:(intros w Hw' [p Hp]; subst w;
                        destruct p as [| [| p]]; simpl in *; lia)) as Hc2.
    rewrite E in Hc2. cbn [snd] in Hc2.
    pose proof (div_double (n - 1) t Ht).
    pose proof (Nat.div_le_compat_l (n - 1) L t ltac:(lia)).
    lia.
Qed.

Theorem fscan_linear (n : nat) (g : nat -> Z) :
  (fscan_cost n g <= 3 * (n - 1))%nat.
Proof.
  unfold fscan_cost, fscan_run.
  pose proof (fscan_from_cost n (n - 1)%nat (first_diff g) 1%nat 1%nat [] 1%nat
                ltac:(lia) ltac:(lia) ltac:(intros w Hw _; lia)) as H.
  rewrite Nat.div_1_r in H. lia.
Qed.
