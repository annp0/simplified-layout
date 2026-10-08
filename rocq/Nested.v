(** * Nested shapes are their leaves, regrouped

    The paper takes shapes flat in Section 4 and in Lemma 1, because "a
    nested shape has the coordinates of the flat shape of its leaves,
    regrouped", and the implementation flattens the same way
    ([Decide.leaves]). This file proves that sentence. Reading a nested
    coordinate's leaves left to right ([cleaves]) is a bijection from
    the coordinates of a nested shape [S] onto those of the flat shape
    [leaves S], and it preserves

    - the index function of a layout: a nested layout [S:D] is the flat
      layout [leaves S : sleaves D] at the leaves ([nev_flat]);
    - the row-major flattening of Definition 1, and so also its inverse
      ([nflat_flat], [nsize_flat]).

    So every statement about flat shapes transfers to nested ones. *)

From Stdlib Require Import Arith Lia ZArith List.
From LayoutAlgebra Require Import Separable.
Import ListNotations.

Open Scope Z_scope.

(** ** Nested shapes, coordinates and strides *)

Inductive nshape : Type := NLeaf (n : nat) | NNode (ss : list nshape).
Inductive ncoord : Type := CLeaf (i : nat) | CNode (cs : list ncoord).
Inductive nstride : Type := SLeaf (d : Z) | SNode (ds : list nstride).

(** Induction over a shape, one child at a time. *)
Section NShapeInd.
  Variable P : nshape -> Prop.
  Hypothesis Hleaf : forall n, P (NLeaf n).
  Hypothesis Hnil : P (NNode []).
  Hypothesis Hcons : forall s ss, P s -> P (NNode ss) -> P (NNode (s :: ss)).

  Fixpoint nshape_ind2 (s : nshape) : P s :=
    match s with
    | NLeaf n => Hleaf n
    | NNode ss =>
        (fix go (l : list nshape) : P (NNode l) :=
           match l with
           | [] => Hnil
           | x :: r => Hcons x r (nshape_ind2 x) (go r)
           end) ss
    end.
End NShapeInd.

(** A coordinate of a shape, and a stride of the same structure, both
    stated one child at a time so that their induction principles are
    the useful ones. *)
Inductive ncoord_ok : nshape -> ncoord -> Prop :=
| nok_leaf : forall n i, (i < n)%nat -> ncoord_ok (NLeaf n) (CLeaf i)
| nok_nil : ncoord_ok (NNode []) (CNode [])
| nok_cons : forall s ss c cs,
    ncoord_ok s c -> ncoord_ok (NNode ss) (CNode cs) ->
    ncoord_ok (NNode (s :: ss)) (CNode (c :: cs)).

Inductive nstride_ok : nshape -> nstride -> Prop :=
| nsok_leaf : forall n d, nstride_ok (NLeaf n) (SLeaf d)
| nsok_nil : nstride_ok (NNode []) (SNode [])
| nsok_cons : forall s ss d ds,
    nstride_ok s d -> nstride_ok (NNode ss) (SNode ds) ->
    nstride_ok (NNode (s :: ss)) (SNode (d :: ds)).

(** ** Leaves, size, index function, flattening *)

Fixpoint leaves (s : nshape) : list nat :=
  match s with
  | NLeaf n => [n]
  | NNode ss =>
      (fix go (l : list nshape) : list nat :=
         match l with [] => [] | x :: r => leaves x ++ go r end) ss
  end.

Fixpoint cleaves (c : ncoord) : list nat :=
  match c with
  | CLeaf i => [i]
  | CNode cs =>
      (fix go (l : list ncoord) : list nat :=
         match l with [] => [] | x :: r => cleaves x ++ go r end) cs
  end.

Fixpoint sleaves (d : nstride) : list Z :=
  match d with
  | SLeaf z => [z]
  | SNode ds =>
      (fix go (l : list nstride) : list Z :=
         match l with [] => [] | x :: r => sleaves x ++ go r end) ds
  end.

Fixpoint nsize (s : nshape) : nat :=
  match s with
  | NLeaf n => n
  | NNode ss =>
      (fix go (l : list nshape) : nat :=
         match l with [] => 1%nat | x :: r => (nsize x * go r)%nat end) ss
  end.

(** Definition 1's index function, by recursion on the shape. *)
Fixpoint nev (d : nstride) (c : ncoord) : Z :=
  match d, c with
  | SLeaf z, CLeaf i => Z.of_nat i * z
  | SNode ds, CNode cs =>
      (fix go (ds : list nstride) (cs : list ncoord) : Z :=
         match ds, cs with
         | x :: r, y :: t => nev x y + go r t
         | _, _ => 0
         end) ds cs
  | _, _ => 0
  end.

(** Definition 1's row-major flattening: the first child is the most
    significant, weighted by the size of everything to its right. *)
Fixpoint nflat (s : nshape) (c : ncoord) : nat :=
  match s, c with
  | NLeaf _, CLeaf i => i
  | NNode ss, CNode cs =>
      (fix go (ss : list nshape) (cs : list ncoord) : nat :=
         match ss, cs with
         | x :: r, y :: t => (nflat x y * nsize (NNode r) + go r t)%nat
         | _, _ => 0%nat
         end) ss cs
  | _, _ => 0%nat
  end.

(** One child at a time, each of these is definitional. *)
Lemma leaves_cons s ss : leaves (NNode (s :: ss)) = leaves s ++ leaves (NNode ss).
Proof. reflexivity. Qed.
Lemma cleaves_cons c cs : cleaves (CNode (c :: cs)) = cleaves c ++ cleaves (CNode cs).
Proof. reflexivity. Qed.
Lemma sleaves_cons d ds : sleaves (SNode (d :: ds)) = sleaves d ++ sleaves (SNode ds).
Proof. reflexivity. Qed.
Lemma nsize_cons s ss : nsize (NNode (s :: ss)) = (nsize s * nsize (NNode ss))%nat.
Proof. reflexivity. Qed.
Lemma nev_cons d ds c cs : nev (SNode (d :: ds)) (CNode (c :: cs)) = nev d c + nev (SNode ds) (CNode cs).
Proof. reflexivity. Qed.
Lemma nflat_cons s ss c cs :
  nflat (NNode (s :: ss)) (CNode (c :: cs))
  = (nflat s c * nsize (NNode ss) + nflat (NNode ss) (CNode cs))%nat.
Proof. reflexivity. Qed.

(** ** The flat counterparts *)

Fixpoint prod (S : list nat) : nat :=
  match S with [] => 1%nat | n :: S' => (n * prod S')%nat end.

Fixpoint fev (D : list Z) (c : list nat) : Z :=
  match D, c with
  | d :: D', x :: c' => Z.of_nat x * d + fev D' c'
  | _, _ => 0
  end.

Fixpoint flat (S : list nat) (c : list nat) : nat :=
  match S, c with
  | _ :: S', x :: c' => (x * prod S' + flat S' c')%nat
  | _, _ => 0%nat
  end.

Lemma coord_ok_length (S c : list nat) : coord_ok S c -> length c = length S.
Proof. induction 1; simpl; congruence. Qed.

Lemma coord_ok_app (A B a b : list nat) :
  coord_ok A a -> coord_ok B b -> coord_ok (A ++ B) (a ++ b).
Proof. intros HA HB. induction HA; simpl; [exact HB | constructor; assumption]. Qed.

Lemma coord_ok_app_inv (A B l : list nat) :
  coord_ok (A ++ B) l -> exists a b, l = a ++ b /\ coord_ok A a /\ coord_ok B b.
Proof.
  revert l. induction A as [| n A IH]; intros l H.
  - exists [], l. split; [reflexivity | split; [constructor | exact H]].
  - simpl in H. inversion H as [| n' S' x c Hx Hc]; subst.
    destruct (IH c Hc) as [a [b [-> [Ha Hb]]]].
    exists (x :: a), b. split; [reflexivity | split; [constructor; assumption | exact Hb]].
Qed.

Lemma app_inv_len {A : Type} (a a' b b' : list A) :
  length a = length a' -> a ++ b = a' ++ b' -> a = a' /\ b = b'.
Proof.
  revert a'. induction a as [| x a IH]; intros a' Hl Heq.
  - destruct a'; [split; [reflexivity | exact Heq] | discriminate].
  - destruct a' as [| x' a']; [discriminate |].
    simpl in Hl, Heq. injection Heq as -> Heq.
    destruct (IH a' ltac:(lia) Heq) as [-> ->]. split; reflexivity.
Qed.

Lemma prod_app (A B : list nat) : prod (A ++ B) = (prod A * prod B)%nat.
Proof. induction A as [| n A IH]; simpl; [lia | rewrite IH; ring]. Qed.

Lemma fev_app (D D' : list Z) (a b : list nat) :
  length D = length a -> fev (D ++ D') (a ++ b) = fev D a + fev D' b.
Proof.
  revert a. induction D as [| d D IH]; intros a Hl.
  - destruct a; [reflexivity | discriminate].
  - destruct a as [| x a]; [discriminate |].
    simpl in Hl |- *. rewrite IH by lia. ring.
Qed.

Lemma flat_app (A B a b : list nat) :
  length A = length a ->
  flat (A ++ B) (a ++ b) = (flat A a * prod B + flat B b)%nat.
Proof.
  revert a. induction A as [| n A IH]; intros a Hl.
  - destruct a; [simpl; lia | discriminate].
  - destruct a as [| x a]; [discriminate |].
    simpl in Hl |- *. rewrite IH, prod_app by lia. ring.
Qed.

(** ** The correspondence *)

Lemma nstride_ok_length (s : nshape) (d : nstride) :
  nstride_ok s d -> length (sleaves d) = length (leaves s).
Proof.
  induction 1; [reflexivity | reflexivity |].
  rewrite sleaves_cons, leaves_cons, !length_app. congruence.
Qed.

(** Leaves of a coordinate are a coordinate of the leaves. *)
Theorem cleaves_ok (s : nshape) (c : ncoord) :
  ncoord_ok s c -> coord_ok (leaves s) (cleaves c).
Proof.
  induction 1 as [n i Hi | | s ss c cs Hs IHs Hss IHss].
  - constructor; [exact Hi | constructor].
  - constructor.
  - rewrite leaves_cons, cleaves_cons. apply coord_ok_app; assumption.
Qed.

(** Every coordinate of the leaves is the leaves of a coordinate. *)
Theorem cleaves_onto (s : nshape) :
  forall l, coord_ok (leaves s) l -> exists c, ncoord_ok s c /\ cleaves c = l.
Proof.
  induction s as [n | | s ss IHs IHss] using nshape_ind2; intros l Hl.
  - simpl in Hl. inversion Hl as [| n' S' i c Hi Hc]; subst.
    inversion Hc; subst.
    exists (CLeaf i). split; [constructor; exact Hi | reflexivity].
  - simpl in Hl. inversion Hl; subst.
    exists (CNode []). split; [constructor | reflexivity].
  - rewrite leaves_cons in Hl.
    destruct (coord_ok_app_inv _ _ _ Hl) as [a [b [-> [Ha Hb]]]].
    destruct (IHs a Ha) as [c [Hc Hca]].
    destruct (IHss b Hb) as [c' [Hc' Hcb]].
    inversion Hc' as [| | s0 ss0 c0 cs0 H0 H1]; subst.
    + exists (CNode [c]). split; [constructor; [exact Hc | constructor] |].
      rewrite cleaves_cons. reflexivity.
    + exists (CNode (c :: c0 :: cs0)). split; [constructor; assumption |].
      rewrite cleaves_cons. reflexivity.
Qed.

(** And no two coordinates have the same leaves. *)
Theorem cleaves_inj (s : nshape) (c c' : ncoord) :
  ncoord_ok s c -> ncoord_ok s c' -> cleaves c = cleaves c' -> c = c'.
Proof.
  intros H. revert c'.
  induction H as [n i Hi | | s ss c cs Hs IHs Hss IHss]; intros c' H' Heq.
  - inversion H'; subst. simpl in Heq. injection Heq as ->. reflexivity.
  - inversion H'; reflexivity.
  - inversion H' as [| | s0 ss0 c1 cs1 Hs1 Hss1]; subst.
    rewrite !cleaves_cons in Heq.
    assert (Hl : length (cleaves c) = length (cleaves c1)).
    { rewrite (coord_ok_length _ _ (cleaves_ok _ _ Hs)).
      rewrite (coord_ok_length _ _ (cleaves_ok _ _ Hs1)). reflexivity. }
    destruct (app_inv_len _ _ _ _ Hl Heq) as [E1 E2].
    rewrite (IHs c1 Hs1 E1).
    specialize (IHss (CNode cs1) Hss1 E2). injection IHss as ->. reflexivity.
Qed.

(** A nested layout is the flat layout of its leaves. *)
Theorem nev_flat (s : nshape) (d : nstride) (c : ncoord) :
  nstride_ok s d -> ncoord_ok s c -> nev d c = fev (sleaves d) (cleaves c).
Proof.
  intros Hd Hc. revert d Hd.
  induction Hc as [n i Hi | | s ss c cs Hs IHs Hss IHss]; intros d Hd.
  - inversion Hd; subst. simpl. ring.
  - inversion Hd; subst. reflexivity.
  - inversion Hd as [| | s0 ss0 d0 ds0 Hd0 Hds0]; subst.
    rewrite nev_cons, sleaves_cons, cleaves_cons.
    rewrite fev_app.
    + rewrite (IHs d0 Hd0), (IHss (SNode ds0) Hds0). reflexivity.
    + rewrite (nstride_ok_length _ _ Hd0).
      symmetry. apply (coord_ok_length _ _ (cleaves_ok _ _ Hs)).
Qed.

Theorem nsize_flat (s : nshape) : nsize s = prod (leaves s).
Proof.
  induction s as [n | | s ss IHs IHss] using nshape_ind2.
  - simpl. lia.
  - reflexivity.
  - rewrite nsize_cons, leaves_cons, prod_app, IHs, IHss. reflexivity.
Qed.

(** Row-major flattening of a nested coordinate is row-major
    flattening of its leaves; so unflattening, its inverse, agrees as
    well. *)
Theorem nflat_flat (s : nshape) (c : ncoord) :
  ncoord_ok s c -> nflat s c = flat (leaves s) (cleaves c).
Proof.
  induction 1 as [n i Hi | | s ss c cs Hs IHs Hss IHss].
  - simpl. lia.
  - reflexivity.
  - rewrite nflat_cons, leaves_cons, cleaves_cons, flat_app.
    + rewrite IHs, IHss, nsize_flat. reflexivity.
    + symmetry. apply (coord_ok_length _ _ (cleaves_ok _ _ Hs)).
Qed.
