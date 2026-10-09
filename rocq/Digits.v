(** * Definition 1, read as digits, and Theorem 1 in its terms

    Section 4 of the paper rewrites "[g] is the layout [T:D] of a flat
    shape [T], read through [unflatten_T]" as a digit sum,

      (T:D)(unflatten_T v) = sum_j s_j * ((v / w_j) mod m_j),

    and [Chain], [Recognize], [Shape], [Complete] and [Coarsest] work
    with the right-hand side ([Chain.dgsum]). This file proves the
    rewriting, from Definition 1's index function and row-major
    unflattening ([zev_digits]), and the converse, that every shape the
    scan builds is such a layout ([triples_of]). Together with
    [Shape.scan_sound_layout] and [Decide.accept_of_axis_layout] they
    give Theorem 1 as the paper states it ([scan_iff_layout]):

      g is a layout of some flat shape of size n  <->  the scan accepts. *)

From Stdlib Require Import Arith Lia ZArith List.
From LayoutAlgebra Require Import Floors Chain Recognize Shape Complete Decide
  Ops Inverse.
Import ListNotations.

Open Scope Z_scope.

(** ** Definition 1, for a flat layout with integer strides *)

(** The index function of [S:D]: index times stride, summed. *)
Fixpoint zev (S : list nat) (D : list Z) (c : list nat) : Z :=
  match S, D, c with
  | _ :: S', d :: D', x :: c' => d * Z.of_nat x + zev S' D' c'
  | _, _, _ => 0
  end.

(** [g] is the layout of some flat shape of size [n], read through
    Definition 1's unflattening ([Inverse.unflatten]). *)
Definition IsLayoutOf (n : nat) (g : nat -> Z) : Prop :=
  exists S D, Forall (fun m => (1 <= m)%nat) S /\ sprod S = n
              /\ length D = length S
              /\ forall v, (v < n)%nat -> g v = zev S D (unflatten S v).

(** The same layout as (weight, radix, stride) triples, innermost first:
    the entry [n] of [n :: S'] has weight [sprod S']. *)
Fixpoint triples (S : list nat) (D : list Z) : list (nat * nat * Z) :=
  match S, D with
  | n :: S', d :: D' => triples S' D' ++ [(sprod S', n, d)]
  | _, _ => []
  end.

(** ** Groundwork *)

Lemma dgsum_app (T U : list (nat * nat * Z)) (v : nat) :
  dgsum (T ++ U) v = dgsum T v + dgsum U v.
Proof.
  induction T as [| [[w m] s] T IH]; simpl; [ring |].
  unfold dgsum in *. simpl. rewrite IH. ring.
Qed.

(** A digit whose weight times radix divides [P] sees only [v mod P]. *)
Lemma digit_mod (v w m P : nat) :
  (1 <= w)%nat -> Nat.divide (w * m) P ->
  ((v / w) mod m = ((v mod P) / w) mod m)%nat.
Proof.
  intros Hw [k Hk].
  rewrite (Nat.Div0.div_mod v P) at 1.
  replace (P * (v / P) + v mod P)%nat
    with ((k * (v / P) * m) * w + v mod P)%nat by (subst P; ring).
  rewrite Nat.div_add_l by lia.
  rewrite Nat.add_comm. apply Nat.Div0.mod_add.
Qed.

Lemma sprod_ge1 (S : list nat) : Forall (fun m => (1 <= m)%nat) S -> (1 <= sprod S)%nat.
Proof.
  induction S as [| n S IH]; intros H; simpl; [lia |].
  inversion H; subst. specialize (IH H3). nia.
Qed.

(** Every entry of [triples S D] has positive weight and radix, and its
    weight times radix divides the size. *)
Lemma triples_props (S : list nat) (D : list Z) :
  Forall (fun m => (1 <= m)%nat) S ->
  Forall (fun e => (1 <= fst (fst e))%nat /\ (1 <= snd (fst e))%nat
                   /\ Nat.divide (fst (fst e) * snd (fst e)) (sprod S)) (triples S D).
Proof.
  revert D. induction S as [| n S IH]; intros D HS; [constructor |].
  destruct D as [| d D]; [constructor |].
  inversion HS as [| ? ? Hn HS']; subst. simpl.
  apply Forall_app. split.
  - eapply Forall_impl; [| exact (IH D HS')].
    intros e [H1 [H2 H3]]. split; [exact H1 | split; [exact H2 |]].
    eapply Nat.divide_trans; [exact H3 |]. exists n. ring.
  - constructor; [| constructor]. simpl.
    pose proof (sprod_ge1 S HS').
    split; [lia | split; [lia |]]. exists 1%nat. ring.
Qed.

Lemma dgsum_mod (T : list (nat * nat * Z)) (v P : nat) :
  Forall (fun e => (1 <= fst (fst e))%nat /\ (1 <= snd (fst e))%nat
                   /\ Nat.divide (fst (fst e) * snd (fst e)) P) T ->
  dgsum T v = dgsum T (v mod P).
Proof.
  induction T as [| [[w m] s] T IH]; intros H; [reflexivity |].
  inversion H as [| ? ? [Hw [Hm Hd]] HT]; subst. simpl in Hw, Hm, Hd.
  rewrite !dgsum_cons, (IH HT).
  rewrite (digit_mod v w m P Hw Hd). reflexivity.
Qed.

(** ** Definition 1 after unflattening is the digit sum *)

Theorem zev_digits (S : list nat) (D : list Z) (v : nat) :
  Forall (fun m => (1 <= m)%nat) S -> (v < sprod S)%nat ->
  zev S D (unflatten S v) = dgsum (triples S D) v.
Proof.
  revert D v. induction S as [| n S IH]; intros D v HS Hv; [reflexivity |].
  destruct D as [| d D]; [reflexivity |].
  inversion HS as [| ? ? Hn HS']; subst.
  pose proof (sprod_ge1 S HS') as HP.
  simpl. rewrite (IH D (v mod sprod S)%nat HS') by (apply Nat.mod_upper_bound; lia).
  rewrite dgsum_app, <- (dgsum_mod (triples S D) v (sprod S)) by (apply triples_props; exact HS').
  simpl in Hv.
  rewrite dgsum_cons, dgsum_nil.
  rewrite (Nat.mod_small (v / sprod S) n)
    by (apply Nat.Div0.div_lt_upper_bound; lia).
  ring.
Qed.

(** ** The triples of a flat shape are a well-formed chain of its size *)

Lemma tsize_snoc (T : list (nat * nat * Z)) (w m : nat) (s : Z) :
  tsize (T ++ [(w, m, s)]) = (tsize T * m)%nat.
Proof.
  induction T as [| [[w1 m1] s1] T IH]; simpl; [lia |].
  rewrite IH. ring.
Qed.

Lemma nof_snoc (T : list (nat * nat * Z)) (w m : nat) (s : Z) :
  nof (T ++ [(w, m, s)]) = (w * m)%nat.
Proof.
  induction T as [| [[w1 m1] s1] T IH]; [reflexivity |].
  simpl. destruct (T ++ [(w, m, s)]) eqn:E.
  - destruct T; discriminate.
  - exact IH.
Qed.

Lemma wf_snoc (T : list (nat * nat * Z)) (w m : nat) (s : Z) :
  wf T -> (T <> [] -> nof T = w) -> w <> 0%nat -> m <> 0%nat ->
  wf (T ++ [(w, m, s)]).
Proof.
  induction T as [| [[w1 m1] s1] T IH]; intros Hwf Hnof Hw Hm.
  - simpl. auto.
  - simpl in Hwf. destruct Hwf as [Hw1 [Hm1 Hrest]].
    destruct T as [| [[w2 m2] s2] T'].
    + simpl. specialize (Hnof ltac:(discriminate)). simpl in Hnof.
      repeat split; auto.
    + destruct Hrest as [Hw2 HwfT].
      assert (H : wf (((w2, m2, s2) :: T') ++ [(w, m, s)])).
      { apply IH; auto. intros _. specialize (Hnof ltac:(discriminate)). exact Hnof. }
      change (((w2, m2, s2) :: T') ++ [(w, m, s)])
        with ((w2, m2, s2) :: (T' ++ [(w, m, s)])) in H.
      exact (conj Hw1 (conj Hm1 (conj Hw2 H))).
Qed.

Lemma wf_snoc_inv (T : list (nat * nat * Z)) (w m : nat) (s : Z) :
  wf (T ++ [(w, m, s)]) -> wf T /\ (T <> [] -> nof T = w).
Proof.
  induction T as [| [[w1 m1] s1] T IH]; intros H.
  - split; [exact I | intros C; contradiction].
  - simpl in H. destruct H as [Hw1 [Hm1 Hrest]].
    destruct T as [| [[w2 m2] s2] T'].
    + simpl in Hrest. destruct Hrest as [Hw _].
      split; [simpl; auto | intros _; simpl; lia].
    + change (((w2, m2, s2) :: T') ++ [(w, m, s)])
        with ((w2, m2, s2) :: (T' ++ [(w, m, s)])) in Hrest.
      destruct Hrest as [Hw2 Hwf'].
      change ((w2, m2, s2) :: (T' ++ [(w, m, s)]))
        with (((w2, m2, s2) :: T') ++ [(w, m, s)]) in Hwf'.
      destruct (IH Hwf') as [HwfT Hnof].
      split.
      * exact (conj Hw1 (conj Hm1 (conj Hw2 HwfT))).
      * intros _. exact (Hnof ltac:(discriminate)).
Qed.

Lemma triples_nil (S : list nat) (D : list Z) :
  length D = length S -> triples S D = [] -> S = [].
Proof.
  destruct S as [| n S]; [reflexivity |].
  destruct D as [| d D]; [discriminate |].
  intros _ H. simpl in H. destruct (triples S D); discriminate.
Qed.

Lemma triples_size (S : list nat) (D : list Z) :
  length D = length S ->
  tsize (triples S D) = sprod S /\ (S <> [] -> nof (triples S D) = sprod S).
Proof.
  revert D. induction S as [| n S IH]; intros D Hlen; [split; [reflexivity | congruence] |].
  destruct D as [| d D]; [discriminate |].
  simpl in Hlen. injection Hlen as Hlen.
  simpl. rewrite tsize_snoc, nof_snoc. destruct (IH D Hlen) as [Ht _].
  rewrite Ht. split; [ring | intros _; ring].
Qed.

Lemma triples_wf (S : list nat) (D : list Z) :
  Forall (fun m => (1 <= m)%nat) S -> length D = length S -> wf (triples S D).
Proof.
  revert D. induction S as [| n S IH]; intros D HS Hlen; [exact I |].
  destruct D as [| d D]; [discriminate |].
  simpl in Hlen. injection Hlen as Hlen.
  inversion HS as [| ? ? Hn HS']; subst.
  pose proof (sprod_ge1 S HS').
  simpl. apply wf_snoc; [apply IH; assumption | | lia | lia].
  intros Hne. apply (triples_size S D Hlen).
  intros ->. destruct D; [contradiction | discriminate].
Qed.

(** ** Every well-formed chain of weight 1 is the triples of a flat shape *)

Definition t_radices (T : list (nat * nat * Z)) : list nat := map (fun e => snd (fst e)) T.
Definition t_strides (T : list (nat * nat * Z)) : list Z := map snd T.

Lemma sprod_app (A B : list nat) : sprod (A ++ B) = (sprod A * sprod B)%nat.
Proof. induction A as [| n A IH]; simpl; [lia | rewrite IH; ring]. Qed.

Lemma sprod_rev (A : list nat) : sprod (rev A) = sprod A.
Proof.
  induction A as [| n A IH]; [reflexivity |].
  simpl. rewrite sprod_app, IH. simpl. ring.
Qed.

Lemma sprod_radices (T : list (nat * nat * Z)) : sprod (t_radices T) = tsize T.
Proof. induction T as [| [[w m] s] T IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma hw_snoc (T : list (nat * nat * Z)) (e : nat * nat * Z) :
  T <> [] -> hw (T ++ [e]) = hw T.
Proof. destruct T as [| [[w m] s] T]; [congruence | reflexivity]. Qed.

Theorem triples_of (T : list (nat * nat * Z)) :
  wf T -> (T <> [] -> hw T = 1%nat) ->
  triples (rev (t_radices T)) (rev (t_strides T)) = T.
Proof.
  induction T as [| [[w m] s] T0 IH] using rev_ind; intros Hwf Hhw; [reflexivity |].
  unfold t_radices, t_strides. rewrite !map_app, !rev_app_distr. simpl.
  fold (t_radices T0) (t_strides T0).
  destruct (wf_snoc_inv T0 w m s Hwf) as [Hwf0 Hnof0].
  rewrite sprod_rev, sprod_radices.
  destruct T0 as [| x T0'] eqn:E0.
  - simpl in Hhw |- *. specialize (Hhw ltac:(discriminate)). subst w. reflexivity.
  - rewrite <- E0 in *.
    assert (Hne : T0 <> []) by (rewrite E0; discriminate).
    assert (Hhw0 : hw T0 = 1%nat).
    { rewrite <- (hw_snoc T0 (w, m, s) Hne). apply Hhw.
      destruct T0; [contradiction | discriminate]. }
    rewrite (IH Hwf0 (fun _ => Hhw0)).
    pose proof (hw_tsize_nof T0 Hwf0 Hne) as Hh.
    rewrite Hhw0, (Hnof0 Hne) in Hh.
    replace w with (tsize T0) by lia. reflexivity.
Qed.

Lemma radices_pos (T : list (nat * nat * Z)) :
  wf T -> Forall (fun m => (1 <= m)%nat) (t_radices T).
Proof.
  induction T as [| [[w m] s] T IH]; intros Hwf; [constructor |].
  simpl in Hwf. destruct Hwf as [_ [Hm Hrest]].
  constructor; [simpl; lia |].
  apply IH. destruct T as [| [[w' m'] s'] T']; [exact I | apply Hrest].
Qed.

(** ** Theorem 1, as the paper states it *)

Theorem scan_iff_layout (n : nat) (g : nat -> Z) :
  (1 <= n)%nat -> g 0%nat = 0 ->
  IsLayoutOf n g <-> exists ws, scan n g = Some ws.
Proof.
  intros Hn Hg0. split.
  - intros [S [D [HS [Hsize [Hlen Hg]]]]].
    destruct S as [| m S'] eqn:ES.
    + simpl in Hsize. subst n. exists []. apply scan_one.
    + rewrite <- ES in *.
      assert (HSne : S <> []) by (rewrite ES; discriminate).
      destruct (triples_size S D Hlen) as [Ht Hnof].
      apply (accept_of_axis_layout n g (triples S D) Hn Hg0).
      * apply triples_wf; assumption.
      * rewrite Ht. exact Hsize.
      * rewrite (Hnof HSne). exact Hsize.
      * intros v Hv. rewrite (Hg v Hv). apply zev_digits; [exact HS | lia].
  - intros [ws Hscan].
    destruct (scan_sound_layout n g ws Hn Hg0 Hscan) as [Hwf [Ht [Hnof Hg]]].
    set (T := shape_of_chain n ws) in *.
    assert (HTne : T <> []) by (intros E; rewrite E in Hnof; simpl in Hnof; lia).
    assert (Hhw : hw T = 1%nat) by (apply (hw_is_one T n); assumption).
    exists (rev (t_radices T)), (rev (t_strides T)).
    split; [| split; [| split]].
    + apply Forall_rev, radices_pos, Hwf.
    + rewrite sprod_rev, sprod_radices. exact Ht.
    + unfold t_radices, t_strides. rewrite !length_rev, !length_map. reflexivity.
    + intros v Hv. rewrite (Hg v Hv).
      rewrite zev_digits.
      * rewrite (triples_of T Hwf (fun _ => Hhw)). reflexivity.
      * apply Forall_rev, radices_pos, Hwf.
      * rewrite sprod_rev, sprod_radices, Ht. exact Hv.
Qed.
