(** * The coarsest shape, and its strides

    The last two claims of the paper's Theorem 1, about the shape
    [shape_of_chain n ws] built from the scan's output:

    - it is the COARSEST: every flat shape of size [n] of which [g] is
      a layout has a chain containing its chain ([scan_coarsest]);
    - its strides are the values of [g] at its weights,
      [s_j = g (w_j)] ([scan_strides]), which is also the last clause
      of Lemma 3 ([dgsum_at_weight]).

    Both rest on [Complete.scan_exact]: the scan's output is determined
    by any chain that represents [g]. *)

From Stdlib Require Import Arith Lia ZArith List.
From LayoutAlgebra Require Import Floors Chain Recognize Shape Complete Decide.
Import ListNotations.

Open Scope Z_scope.

(** The chain of a shape: its weights, in order. *)
Definition weights (T : list (nat * nat * Z)) : list nat :=
  map (fun e => fst (fst e)) T.

Lemma weights_coeffs (prev : Z) (T : list (nat * nat * Z)) :
  map fst (coeffs prev T) = weights T.
Proof.
  revert prev. induction T as [| [[w m] s] T IH]; intros prev; [reflexivity |].
  rewrite coeffs_cons. simpl. f_equal. apply IH.
Qed.

Lemma weights_drop1 (T : list (nat * nat * Z)) :
  incl (weights (drop1 T)) (weights T).
Proof.
  induction T as [| [[w m] s] T IH]; [intros x Hx; exact Hx |].
  simpl. destruct (Nat.eqb m 1); simpl.
  - intros x Hx. right. apply IH, Hx.
  - intros x [Hx | Hx]; [left; exact Hx | right; apply IH, Hx].
Qed.

Lemma weights_shape_of (n : nat) (prev : Z) (ws : list (nat * Z)) :
  weights (shape_of n prev ws) = map fst ws.
Proof.
  revert prev. induction ws as [| [w a] ws IH]; intros prev; [reflexivity |].
  rewrite shape_of_cons. simpl. f_equal. apply IH.
Qed.

Lemma weights_with_one (ws : list (nat * Z)) :
  incl (map fst (with_one ws)) (1%nat :: map fst ws).
Proof.
  destruct ws as [| [w a] ws]; simpl.
  - intros x [Hx | []]. left. exact Hx.
  - destruct (Nat.eqb_spec w 1) as [-> | Hne]; simpl.
    + intros x Hx. right. exact Hx.
    + intros x Hx. exact Hx.
Qed.

Lemma hw_in_weights (T : list (nat * nat * Z)) :
  T <> [] -> In (hw T) (weights T).
Proof.
  destruct T as [| [[w m] s] T]; [contradiction | intros _; left; reflexivity].
Qed.

(** ** Theorem 1: the scan's shape is the coarsest *)

Theorem scan_coarsest (n : nat) (g : nat -> Z) (ws : list (nat * Z))
        (T : list (nat * nat * Z)) :
  (1 <= n)%nat -> g 0%nat = 0 -> scan n g = Some ws ->
  wf T -> tsize T = n -> nof T = n ->
  (forall v, (v < n)%nat -> g v = dgsum T v) ->
  incl (weights (shape_of_chain n ws)) (weights T).
Proof.
  intros Hn Hg0 Hscan Hwf Ht Hnof Hval.
  assert (HT : T <> []) by (intro E; subst T; simpl in Hnof; lia).
  assert (H1 : In 1%nat (weights T)).
  { rewrite <- (hw_is_one T n Hn Hwf HT Ht Hnof). apply hw_in_weights, HT. }
  unfold shape_of_chain. rewrite weights_shape_of.
  intros x Hx. apply weights_with_one in Hx.
  destruct Hx as [<- | Hx]; [exact H1 |].
  destruct (Nat.eq_dec n 1) as [-> | Hne].
  - rewrite scan_one in Hscan. injection Hscan as <-. destruct Hx.
  - destruct (chain_of_axis_layout n g T ltac:(lia) Hwf Ht Hnof Hval)
      as [Hch HR].
    apply weights_drop1. rewrite <- (weights_coeffs 0).
    exact (scan_minimal n g _ ws Hn Hg0 Hch HR Hscan x Hx).
Qed.

(** ** Lemma 3, last clause: a digit sum at one of its weights *)

Lemma wf_tail (w m : nat) (s : Z) (T : list (nat * nat * Z)) :
  wf ((w, m, s) :: T) -> wf T.
Proof.
  intros H. simpl in H. destruct H as [_ [_ H]].
  destruct T as [| [[w' m'] s'] T']; [exact I | apply H].
Qed.

(** Every weight of a well-formed shape is a multiple of the head
    weight, and at least it. *)
Lemma wf_weights_hw (T : list (nat * nat * Z)) :
  wf T ->
  Forall (fun e => Nat.divide (hw T) (fst (fst e)) /\ (hw T <= fst (fst e))%nat) T.
Proof.
  induction T as [| [[w m] s] T IH]; intros Hwf; [constructor |].
  pose proof (wf_tail _ _ _ _ Hwf) as HwfT.
  simpl in Hwf. destruct Hwf as [Hw [Hm Hrest]].
  constructor.
  - simpl. split; [apply Nat.divide_refl | lia].
  - destruct T as [| [[w' m'] s'] T']; [constructor |].
    destruct Hrest as [Hw' _].
    specialize (IH HwfT). simpl (hw _) in IH |- *.
    eapply Forall_impl; [| exact IH]. intros e [Hd Hle].
    split.
    + apply (Nat.divide_trans w w'); [exists m; nia | exact Hd].
    + nia.
Qed.

(** Below every weight, every digit is zero. *)
Lemma dgsum_small (T : list (nat * nat * Z)) (v : nat) :
  Forall (fun e => (v < fst (fst e))%nat) T -> dgsum T v = 0.
Proof.
  induction T as [| [[w m] s] T IH]; intros H; [reflexivity |].
  inversion H as [| ? ? Hh Ht]; subst. simpl in Hh.
  rewrite dgsum_cons, (IH Ht), (Nat.div_small v w Hh).
  rewrite Nat.Div0.mod_0_l. simpl. ring.
Qed.

(** At its own weight a digit reads [1], every earlier digit reads [0]
    because the weight is a multiple of the next radix boundary, and
    every later digit reads [0] because its weight is larger. So the
    digit sum there is that digit's stride. *)
Lemma dgsum_at_weight (T : list (nat * nat * Z)) (w m : nat) (s : Z) :
  wf T -> Forall (fun e => (2 <= snd (fst e))%nat) T -> In (w, m, s) T ->
  dgsum T w = s.
Proof.
  induction T as [| [[w0 m0] s0] T IH]; intros Hwf H2 Hin; [destruct Hin |].
  pose proof (wf_tail _ _ _ _ Hwf) as HwfT.
  inversion H2 as [| ? ? H2h H2t]; subst. simpl in H2h.
  assert (Hwf0 := Hwf). simpl in Hwf0. destruct Hwf0 as [Hw0 [Hm0 Hrest]].
  rewrite dgsum_cons.
  destruct Hin as [Heq | Hin].
  - injection Heq as <- <- <-.
    rewrite Nat.div_same by exact Hw0. rewrite Nat.mod_1_l by lia.
    destruct T as [| [[w' m'] s'] T'].
    + simpl. ring.
    + destruct Hrest as [Hw' _].
      rewrite dgsum_small; [ring |].
      pose proof (wf_weights_hw _ HwfT) as Hge. simpl (hw _) in Hge.
      eapply Forall_impl; [| exact Hge]. intros e [_ Hle]. nia.
  - destruct T as [| [[w' m'] s'] T']; [destruct Hin |].
    destruct Hrest as [Hw' _].
    pose proof (wf_weights_hw _ HwfT) as Hdiv. simpl (hw _) in Hdiv.
    rewrite Forall_forall in Hdiv.
    destruct (Hdiv (w, m, s) Hin) as [[q Hq] _]. simpl in Hq.
    replace ((w / w0) mod m0)%nat with 0%nat.
    + rewrite (IH HwfT H2t Hin). ring.
    + rewrite Hq, Hw'.
      replace (q * (w0 * m0))%nat with ((q * m0) * w0)%nat by ring.
      rewrite Nat.div_mul by exact Hw0.
      symmetry. apply Nat.Div0.mod_mul.
Qed.

(** ** Theorem 1: the strides are [s_j = g (w_j)] *)

(** Every weight the scan records lies below [n]. *)
Lemma scan_weights_lt (n : nat) (g : nat -> Z) (ws : list (nat * Z)) :
  (1 <= n)%nat -> g 0%nat = 0 -> scan n g = Some ws ->
  Forall (fun p => (fst p < n)%nat) ws.
Proof.
  intros Hn Hg0 Hscan.
  destruct (scan_sound n g ws Hn Hg0 Hscan) as [Hch HR].
  rewrite (scan_exact n g ws Hn Hg0 Hch HR) in Hscan.
  injection Hscan as Heq. rewrite <- Heq.
  apply Forall_forall. intros p Hp. unfold below in Hp.
  apply filter_In in Hp. destruct Hp as [_ Hp]. now apply Nat.ltb_lt.
Qed.

(** A chain below [n] gives radices of at least [2]: each is the next
    weight over this one, and the chain strictly increases. *)
Lemma shape_of_radices_ge2 (n : nat) :
  forall ws prev p lo, (1 <= lo)%nat -> chain_ok p lo n ws ->
    Forall (fun q => (fst q < n)%nat) ws ->
    Forall (fun e => (2 <= snd (fst e))%nat) (shape_of n prev ws).
Proof.
  induction ws as [| [w a] ws IH]; intros prev p lo Hlo Hc Hlt; [constructor |].
  simpl in Hc. destruct Hc as [Hdp [Hdn [Hlow Hrest]]].
  inversion Hlt as [| ? ? Hwn Hlt']; subst. simpl in Hwn.
  rewrite shape_of_cons. constructor.
  - simpl. destruct ws as [| [w' a'] ws']; simpl.
    + destruct Hdn as [q Hq]. rewrite Hq, Nat.div_mul by lia. nia.
    + simpl in Hrest. destruct Hrest as [[q Hq] [_ [Hge _]]].
      rewrite Hq, Nat.div_mul by lia. nia.
  - eapply IH; [| exact Hrest | exact Hlt']. lia.
Qed.

Theorem scan_strides (n : nat) (g : nat -> Z) (ws : list (nat * Z)) :
  (2 <= n)%nat -> g 0%nat = 0 -> scan n g = Some ws ->
  forall w m s, In (w, m, s) (shape_of_chain n ws) -> s = g w.
Proof.
  intros Hn Hg0 Hscan w m s Hin.
  pose proof (scan_sound_layout n g ws ltac:(lia) Hg0 Hscan) as Hsl.
  cbv zeta in Hsl. destruct Hsl as [Hwf [_ [_ Hval]]].
  destruct (scan_sound n g ws ltac:(lia) Hg0 Hscan) as [Hch _].
  assert (Hch1 : chain_ok 1%nat 1%nat n (with_one ws))
    by (apply chain_ok_with_one; [lia | exact Hch]).
  assert (Hlt : Forall (fun p => (fst p < n)%nat) (with_one ws)).
  { pose proof (scan_weights_lt n g ws ltac:(lia) Hg0 Hscan) as H.
    destruct ws as [| [w0 a0] ws']; simpl.
    - constructor; [simpl; lia | constructor].
    - destruct (Nat.eqb w0 1); [exact H | constructor; [simpl; lia | exact H]]. }
  assert (H2 : Forall (fun e => (2 <= snd (fst e))%nat) (shape_of_chain n ws))
    by (eapply shape_of_radices_ge2; [| exact Hch1 | exact Hlt]; lia).
  assert (Hwn : (w < n)%nat).
  { assert (Hw : In w (weights (shape_of_chain n ws)))
      by (apply in_map_iff; exists (w, m, s); split; [reflexivity | exact Hin]).
    unfold shape_of_chain in Hw. rewrite weights_shape_of in Hw.
    apply in_map_iff in Hw. destruct Hw as [p [<- Hp]].
    rewrite Forall_forall in Hlt. exact (Hlt p Hp). }
  rewrite (Hval w Hwn). symmetry.
  exact (dgsum_at_weight _ w m s Hwf H2 Hin).
Qed.
