(** * The whole decision procedure

    [Separable] reduces the question to one axis; [Recognize] and
    [Shape] answer it there. This file puts the two together, so the
    result is about what [Decide.strided_form] actually runs:

      - take [k] to be the value at the origin and [g_i v] to be
        [f (v * e_i) - k];
      - check separability, one pass over the box;
      - run the scan on each [g_i].

    [decide_iff] says those checks succeed exactly when [f] is the
    index function of a layout over a refinement of the domain, plus a
    constant. Soundness is what stops a wrong address formula being
    emitted; completeness is what makes "decided, not searched" true --
    no simplification is missed. *)

From Coq Require Import Arith Lia ZArith List.
From LayoutAlgebra Require Import Floors Chain Recognize Shape Complete Separable.
Import ListNotations.

Open Scope Z_scope.

(** The per-axis check, as the implementation runs it. *)
Inductive AllAccept : list nat -> list (nat -> Z) -> Prop :=
| AA_nil : AllAccept [] []
| AA_cons : forall n S g gs,
    (exists ws, scan n g = Some ws) ->
    AllAccept S gs -> AllAccept (n :: S) (g :: gs).

(** Every axis function vanishes at the origin, by construction: it is
    a difference from the origin's value. This is the hypothesis both
    [scan_sound_layout] and [scan_complete] need. *)
Lemma axis_gs_head_zero (S' : list nat) (f : list nat -> Z) :
  (fun v => f (v :: origin S') - f (0%nat :: origin S')) 0%nat = 0.
Proof. simpl. ring. Qed.

(** ** Soundness: the checks passing means the layout is real *)

Lemma axis_layouts_of_accept (S : list nat) (f : list nat -> Z) :
  sizes_pos S -> AllAccept S (axis_gs S f) -> AxisLayoutsEx S (axis_gs S f).
Proof.
  revert f. induction S as [| n S IH]; intros f Hp HA.
  - exists []. constructor.
  - simpl in HA.
    inversion HA as [| n0 S0 g0 gs0 [ws Hscan] HA' Heq1 Heq2]; subst.
    assert (Hn : (1 <= n)%nat) by (eapply sizes_pos_head; exact Hp).
    assert (Hp' : sizes_pos S) by (eapply sizes_pos_tail; exact Hp).
    destruct (IH (fun c => f (0%nat :: c)) Hp' HA') as [Ts' HAL'].
    pose proof (scan_sound_layout n
                  (fun v => f (v :: origin S) - f (0%nat :: origin S)) ws
                  Hn (axis_gs_head_zero S f) Hscan) as Hsl.
    cbv zeta in Hsl. destruct Hsl as [Hwf [Htsz [Hnof Hval]]].
    exists (shape_of_chain n ws :: Ts').
    simpl. constructor; assumption.
Qed.

Theorem decide_sound (S : list nat) (f : list nat -> Z) :
  sizes_pos S -> Separable S f -> AllAccept S (axis_gs S f) -> IsRefined S f.
Proof.
  intros Hp Hsep HA.
  apply (proj2 (separable_iff S f Hp)).
  split; [exact Hsep | apply axis_layouts_of_accept; assumption].
Qed.

(** ** Completeness: a real layout passes the checks

    The scan is stated over CHAINS, whose weights strictly increase, so
    a shape carrying a radix-1 digit has to be normalized first: such a
    digit is identically zero, and dropping it reconnects the chain
    because the weight it would have contributed is its predecessor's.
    Nothing else about the shape changes. *)

Fixpoint drop1 (T : list (nat * nat * Z)) : list (nat * nat * Z) :=
  match T with
  | [] => []
  | (w, m, s) :: rest => if Nat.eqb m 1 then drop1 rest else (w, m, s) :: drop1 rest
  end.

Lemma dgsum_drop1 (T : list (nat * nat * Z)) (v : nat) :
  dgsum (drop1 T) v = dgsum T v.
Proof.
  induction T as [| [[w m] s] T IH]; [reflexivity |].
  simpl. destruct (Nat.eqb_spec m 1) as [-> | Hne].
  - rewrite IH. rewrite Nat.mod_1_r. simpl. ring.
  - rewrite dgsum_cons, IH. reflexivity.
Qed.

Lemma tsize_drop1 (T : list (nat * nat * Z)) : tsize (drop1 T) = tsize T.
Proof.
  induction T as [| [[w m] s] T IH]; [reflexivity |].
  simpl. destruct (Nat.eqb_spec m 1) as [-> | Hne]; simpl; lia.
Qed.

(** Every weight of a well-formed shape divides its [nof]. *)
Lemma wf_weights_divide (T : list (nat * nat * Z)) (n : nat) :
  wf T -> nof T = n -> Forall (fun e => Nat.divide (fst (fst e)) n) T.
Proof.
  revert n. induction T as [| [[w m] s] T IH]; intros n Hwf Hnof; [constructor |].
  simpl in Hwf. destruct Hwf as [Hw [Hm Hrest]].
  destruct T as [| [[w' m'] s'] T'].
  - simpl in Hnof. constructor; [simpl; exists m; lia | constructor].
  - destruct Hrest as [Hw' HwfT].
    assert (Hnof' : nof ((w', m', s') :: T') = n) by exact Hnof.
    specialize (IH n HwfT Hnof').
    constructor; [| exact IH].
    inversion IH as [| ? ? Hh ?]; subst.
    (* w divides the next weight w * m, which divides n *)
    simpl. apply (Nat.divide_trans w (w * m)%nat); [exists m; lia | exact Hh].
Qed.

(** The head weight times the size is the range: [w_1 * prod m_j =
    w_k * m_k]. With [tsize T = nof T = n] and [n >= 1] it forces
    [w_1 = 1], which is what a chain needs. *)
Lemma hw_tsize_nof (T : list (nat * nat * Z)) :
  wf T -> T <> [] -> (hw T * tsize T)%nat = nof T.
Proof.
  induction T as [| [[w m] s] T IH]; intros Hwf Hne; [contradiction |].
  simpl in Hwf. destruct Hwf as [Hw [Hm Hrest]].
  destruct T as [| [[w' m'] s'] T'].
  - simpl. lia.
  - destruct Hrest as [Hw' HwfT].
    specialize (IH HwfT ltac:(discriminate)).
    simpl (hw _). rewrite tsize_cons.
    change (nof ((w, m, s) :: (w', m', s') :: T'))
      with (nof ((w', m', s') :: T')).
    simpl (hw _) in IH. rewrite <- IH, Hw'. lia.
Qed.

Lemma hw_is_one (T : list (nat * nat * Z)) (n : nat) :
  (1 <= n)%nat -> wf T -> T <> [] -> tsize T = n -> nof T = n -> hw T = 1%nat.
Proof.
  intros Hn Hwf Hne Ht Hnof.
  pose proof (hw_tsize_nof T Hwf Hne) as H. rewrite Ht, Hnof in H. nia.
Qed.

(** [drop1] keeps the head weight, unless it empties the list. *)
Lemma hw_drop1 (T : list (nat * nat * Z)) :
  wf T -> drop1 T <> [] -> hw (drop1 T) = hw T.
Proof.
  induction T as [| [[w m] s] T IH]; intros Hwf Hne; [contradiction |].
  simpl in Hwf. destruct Hwf as [Hw [Hm Hrest]].
  simpl in Hne |- *. destruct (Nat.eqb_spec m 1) as [-> | Hm1].
  - (* dropped: the next weight is w * 1 = w *)
    destruct T as [| [[w' m'] s'] T']; [contradiction |].
    destruct Hrest as [Hw' HwfT].
    rewrite (IH HwfT Hne). simpl. lia.
  - reflexivity.
Qed.

(** When everything is dropped, every radix was 1, so the range is the
    head weight. *)
Lemma nof_all_ones (T : list (nat * nat * Z)) :
  wf T -> T <> [] -> drop1 T = [] -> nof T = hw T.
Proof.
  induction T as [| [[w m] s] T IH]; intros Hwf Hne Hd; [contradiction |].
  simpl in Hwf. destruct Hwf as [Hw [Hm Hrest]].
  simpl in Hd. destruct (Nat.eqb_spec m 1) as [-> | Hm1]; [| discriminate].
  destruct T as [| [[w' m'] s'] T'].
  - simpl. lia.
  - destruct Hrest as [Hw' HwfT].
    change (nof ((w, 1%nat, s) :: (w', m', s') :: T'))
      with (nof ((w', m', s') :: T')).
    rewrite (IH HwfT ltac:(discriminate) Hd). simpl. lia.
Qed.

Lemma nof_drop1 (T : list (nat * nat * Z)) :
  wf T -> drop1 T <> [] -> nof (drop1 T) = nof T.
Proof.
  induction T as [| [[w m] s] T IH]; intros Hwf Hne; [contradiction |].
  simpl in Hwf. destruct Hwf as [Hw [Hm Hrest]].
  assert (HwfT : wf T)
    by (destruct T as [| [[w' m'] s'] T']; [exact I | apply Hrest]).
  simpl in Hne |- *. destruct (Nat.eqb_spec m 1) as [-> | Hm1].
  - (* this entry goes; the next weight was w * 1 = w anyway *)
    destruct T as [| [[w' m'] s'] T']; [contradiction |].
    exact (IH HwfT Hne).
  - destruct (drop1 T) as [| x xs] eqn:Hd.
    + (* nothing survives after this entry, so the range is its own *)
      destruct T as [| [[w' m'] s'] T']; [reflexivity |].
      rewrite (nof_all_ones _ HwfT ltac:(discriminate) Hd).
      simpl. destruct Hrest as [Hw' _]. lia.
    + destruct T as [| [[w' m'] s'] T']; [simpl in Hd; discriminate |].
      rewrite nof_cons_cons. apply (IH HwfT). discriminate.
Qed.

Lemma wf_drop1 (T : list (nat * nat * Z)) : wf T -> wf (drop1 T).
Proof.
  induction T as [| [[w m] s] T IH]; intros Hwf; [exact I |].
  simpl in Hwf. destruct Hwf as [Hw [Hm Hrest]].
  assert (HwfT : wf T)
    by (destruct T as [| [[w' m'] s'] T']; [exact I | apply Hrest]).
  simpl. destruct (Nat.eqb_spec m 1) as [-> | Hm1]; [exact (IH HwfT) |].
  split; [exact Hw |]. split; [exact Hm |].
  destruct (drop1 T) as [| [[w2 m2] s2] rest2] eqn:E; [exact I |].
  split; [| exact (IH HwfT)].
  (* the surviving next weight is the original next weight *)
  destruct T as [| [[w' m'] s'] T']; [simpl in E; discriminate |].
  destruct Hrest as [Hw' _].
  assert (Hh : hw (drop1 ((w', m', s') :: T')) = hw ((w', m', s') :: T'))
    by (apply hw_drop1; [exact HwfT | rewrite E; discriminate]).
  rewrite E in Hh. simpl in Hh. lia.
Qed.

Lemma drop1_radices_ge2 (T : list (nat * nat * Z)) :
  wf T -> Forall (fun e => (2 <= snd (fst e))%nat) (drop1 T).
Proof.
  induction T as [| [[w m] s] T IH]; intros Hwf; [constructor |].
  simpl in Hwf. destruct Hwf as [Hw [Hm Hrest]].
  assert (HwfT : wf T)
    by (destruct T as [| [[w' m'] s'] T']; [exact I | apply Hrest]).
  simpl. destruct (Nat.eqb_spec m 1) as [-> | Hm1]; [exact (IH HwfT) |].
  constructor; [simpl; lia | exact (IH HwfT)].
Qed.

(** A well-formed shape whose radices all exceed 1 gives a chain. *)
Lemma chain_ok_coeffs (n : nat) :
  forall T prev p lo,
    wf T ->
    Forall (fun e => (2 <= snd (fst e))%nat) T ->
    Forall (fun e => Nat.divide (fst (fst e)) n) T ->
    (T <> [] -> Nat.divide p (hw T) /\ (lo <= hw T)%nat) ->
    chain_ok p lo n (coeffs prev T).
Proof.
  induction T as [| [[w m] s] T IH]; intros prev p lo Hwf H2 Hdv Hhead; [exact I |].
  simpl in Hwf. destruct Hwf as [Hw [Hm Hrest]].
  destruct (Hhead ltac:(discriminate)) as [Hp Hlo]. simpl in Hp, Hlo.
  inversion H2 as [| ? ? H2h H2t]; subst. simpl in H2h.
  inversion Hdv as [| ? ? Hdh Hdt]; subst. simpl in Hdh.
  rewrite coeffs_cons. simpl.
  split; [exact Hp |]. split; [exact Hdh |]. split; [exact Hlo |].
  destruct T as [| [[w' m'] s'] T'].
  - rewrite coeffs_nil. exact I.
  - destruct Hrest as [Hw' HwfT].
    apply (IH (Z.of_nat m * s) w (S w) HwfT H2t Hdt).
    intros _. simpl. split; [exists m; lia | nia].
Qed.

(** An axis of size 1 is accepted with no digits at all --- which is
    also what [Decide.strided_form] short-circuits to for [n = 1]. *)
Lemma scan_one (g : nat -> Z) : scan 1 g = Some [].
Proof. reflexivity. Qed.

(** A real per-axis layout is accepted by the scan. *)
Lemma accept_of_axis_layout (n : nat) (g : nat -> Z) (T : list (nat * nat * Z)) :
  (1 <= n)%nat -> g 0%nat = 0 ->
  wf T -> tsize T = n -> nof T = n ->
  (forall v, (v < n)%nat -> g v = dgsum T v) ->
  exists ws, scan n g = Some ws.
Proof.
  intros Hn Hg0 Hwf Ht Hnof Hval.
  destruct (Nat.eq_dec n 1) as [-> | Hne].
  - exists []. apply scan_one.
  - (* radix-1 digits must go first: a chain's weights strictly increase *)
    assert (Hd : drop1 T <> []).
    { intro H. pose proof (tsize_drop1 T) as Ht1.
      rewrite H in Ht1. simpl in Ht1. lia. }
    assert (HwfD : wf (drop1 T)) by (apply wf_drop1; exact Hwf).
    assert (HnofD : nof (drop1 T) = n)
      by (rewrite (nof_drop1 T Hwf Hd); exact Hnof).
    assert (HtD : tsize (drop1 T) = n) by (rewrite tsize_drop1; exact Ht).
    assert (HhwD : hw (drop1 T) = 1%nat)
      by (apply (hw_is_one (drop1 T) n); assumption).
    assert (Hch : chain_ok 1%nat 1%nat n (coeffs 0 (drop1 T))).
    { apply chain_ok_coeffs.
      - exact HwfD.
      - apply drop1_radices_ge2; exact Hwf.
      - apply (wf_weights_divide (drop1 T) n); assumption.
      - intros _. rewrite HhwD. split; [apply Nat.divide_refl | lia]. }
    assert (HR : Represents n g (coeffs 0 (drop1 T))).
    { intros v Hv. rewrite (Hval v Hv), <- dgsum_drop1.
      apply (dgsum_is_fsum (drop1 T) v HwfD). rewrite HnofD; exact Hv. }
    exact (scan_complete n g (coeffs 0 (drop1 T)) Hn Hg0 Hch HR).
Qed.

Lemma allaccept_of_axis_layouts (S : list nat) (f : list nat -> Z) Ts :
  sizes_pos S -> AxisLayouts S (axis_gs S f) Ts -> AllAccept S (axis_gs S f).
Proof.
  revert f Ts. induction S as [| n S IH]; intros f Ts Hp HAL.
  - constructor.
  - simpl in HAL |- *.
    inversion HAL as [| n0 S0 g0 gs0 T0 Ts0 Hwf Ht Hnof Hval HAL' Heq1 Heq2 Heq3];
      subst.
    (* [subst] has replaced the axis size by [tsize T0] *)
    assert (Hn : (1 <= tsize T0)%nat) by (eapply sizes_pos_head; exact Hp).
    assert (Hp' : sizes_pos S) by (eapply sizes_pos_tail; exact Hp).
    constructor.
    + apply (accept_of_axis_layout _ _ T0); try assumption; try reflexivity.
      apply axis_gs_head_zero.
    + apply (IH (fun c => f (0%nat :: c)) Ts0 Hp' HAL').
Qed.

Theorem decide_complete (S : list nat) (f : list nat -> Z) :
  sizes_pos S -> IsRefined S f -> Separable S f /\ AllAccept S (axis_gs S f).
Proof.
  intros Hp HIR.
  destruct (proj1 (separable_iff S f Hp) HIR) as [Hsep [Ts HAL]].
  split; [exact Hsep | eapply allaccept_of_axis_layouts; eassumption].
Qed.

(** ** The decision procedure, decided

    The checks [Decide.strided_form] runs --- separability in one pass,
    then the scan on each axis --- succeed exactly when the map is the
    index function of a layout over a refinement of its domain, plus a
    constant. *)
Theorem decide_iff (S : list nat) (f : list nat -> Z) :
  sizes_pos S ->
  (IsRefined S f <-> Separable S f /\ AllAccept S (axis_gs S f)).
Proof.
  intros Hp. split.
  - apply decide_complete; exact Hp.
  - intros [Hsep HA]. apply decide_sound; assumption.
Qed.
