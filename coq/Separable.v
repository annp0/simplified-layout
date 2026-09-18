(** * Separability: the paper's Lemma 2

    [Recognize] and [Shape] answer the question one axis at a time.
    This file is the reduction TO one axis, which is what makes the
    whole of [Decide.strided_form] verified rather than just its core.

    The shape is taken flat: a nested shape has the coordinates of the
    flat shape of its leaves, regrouped, which is how the
    implementation treats it too ([Decide.leaves]).

    The statement follows the implementation exactly. Writing [k] for
    the value at the origin and

      g_i v = f (v * e_i) - k

    for the value along axis [i] with every other index zero, [f] is
    the index function of a layout over a refinement of [S], plus [k],
    exactly when

      f c = k + sum_i g_i (c_i)         (separability, one pass)

    and each [g_i] is a layout of a flat shape of size [n_i] (which is
    what [Recognize.scan] decides). The content is that the [g_i] are
    FORCED --- there is nothing to search for, they are read off the
    unit coordinates. *)

From Coq Require Import Arith Lia ZArith List.
From LayoutAlgebra Require Import Floors Chain Recognize Shape.
Import ListNotations.

Open Scope Z_scope.

(** ** Multi-axis coordinates *)

Inductive coord_ok : list nat -> list nat -> Prop :=
| cok_nil : coord_ok [] []
| cok_cons : forall n S x c,
    (x < n)%nat -> coord_ok S c -> coord_ok (n :: S) (x :: c).

Fixpoint origin (S : list nat) : list nat :=
  match S with
  | [] => []
  | _ :: S' => 0%nat :: origin S'
  end.

Definition sizes_pos (S : list nat) : Prop := Forall (fun n => (1 <= n)%nat) S.

Lemma sizes_pos_tail (n : nat) (S : list nat) :
  sizes_pos (n :: S) -> sizes_pos S.
Proof. intros H. now inversion H. Qed.

Lemma sizes_pos_head (n : nat) (S : list nat) :
  sizes_pos (n :: S) -> (1 <= n)%nat.
Proof. intros H. inversion H as [| ? ? Hh ?]. exact Hh. Qed.

Lemma coord_ok_origin (S : list nat) : sizes_pos S -> coord_ok S (origin S).
Proof.
  induction S as [| n S IH]; intros Hp; [constructor |].
  simpl. constructor.
  - pose proof (sizes_pos_head _ _ Hp). lia.
  - apply IH. eapply sizes_pos_tail; exact Hp.
Qed.

(** ** The index function of a layout over a refinement *)

(** One digit sum per axis. *)
Fixpoint mdgsum (Ts : list (list (nat * nat * Z))) (c : list nat) : Z :=
  match Ts, c with
  | T :: Ts', x :: c' => dgsum T x + mdgsum Ts' c'
  | _, _ => 0
  end.

(** A refinement of [S]: one flat shape per axis, of that axis's size.
    [nof T = n] as well as [tsize T = n], so the digits of axis [i]
    cover [[0, n_i)] --- both hold for the shapes [Shape.shape_of_chain]
    builds, since it forces weight 1 into the chain. *)
Inductive Refined : list nat -> list (list (nat * nat * Z)) -> Prop :=
| Refined_nil : Refined [] []
| Refined_cons : forall n S T Ts,
    wf T -> tsize T = n -> nof T = n -> Refined S Ts ->
    Refined (n :: S) (T :: Ts).

Definition IsRefined (S : list nat) (f : list nat -> Z) : Prop :=
  exists k Ts, Refined S Ts /\ (forall c, coord_ok S c -> f c = k + mdgsum Ts c).

(** ** The forced per-axis functions *)

(** [axis_gs S f] is the list of [g_i], read off the unit coordinates.
    Pushing a [0] onto the front of [f]'s argument is what moves to the
    next axis, so no indices are needed. *)
Fixpoint axis_gs (S : list nat) (f : list nat -> Z) : list (nat -> Z) :=
  match S with
  | [] => []
  | _ :: S' =>
      (fun v => f (v :: origin S') - f (0%nat :: origin S'))
      :: axis_gs S' (fun c => f (0%nat :: c))
  end.

Fixpoint gsum (gs : list (nat -> Z)) (c : list nat) : Z :=
  match gs, c with
  | g :: gs', x :: c' => g x + gsum gs' c'
  | _, _ => 0
  end.

(** Separability: one pass over the box. *)
Definition Separable (S : list nat) (f : list nat -> Z) : Prop :=
  forall c, coord_ok S c -> f c = f (origin S) + gsum (axis_gs S f) c.

(** Each [g_i] is a layout of a flat shape of size [n_i], with the
    shape named. *)
Inductive AxisLayouts :
  list nat -> list (nat -> Z) -> list (list (nat * nat * Z)) -> Prop :=
| AL_nil : AxisLayouts [] [] []
| AL_cons : forall n S g gs T Ts,
    wf T -> tsize T = n -> nof T = n ->
    (forall v, (v < n)%nat -> g v = dgsum T v) ->
    AxisLayouts S gs Ts ->
    AxisLayouts (n :: S) (g :: gs) (T :: Ts).

Definition AxisLayoutsEx (S : list nat) (gs : list (nat -> Z)) : Prop :=
  exists Ts, AxisLayouts S gs Ts.

(** ** Groundwork *)

Lemma dgsum_zero (T : list (nat * nat * Z)) : dgsum T 0%nat = 0.
Proof.
  induction T as [| [[w m] s] T IH]; [reflexivity |].
  rewrite dgsum_cons, IH.
  rewrite Nat.Div0.div_0_l, Nat.Div0.mod_0_l. simpl. ring.
Qed.

Lemma mdgsum_origin (S : list nat) (Ts : list (list (nat * nat * Z))) :
  Refined S Ts -> mdgsum Ts (origin S) = 0.
Proof.
  induction 1 as [| n S T Ts Hwf Ht Hn HR IH]; [reflexivity |].
  simpl. rewrite dgsum_zero, IH. ring.
Qed.

Lemma Refined_of_AxisLayouts (S : list nat) (gs : list (nat -> Z)) Ts :
  AxisLayouts S gs Ts -> Refined S Ts.
Proof.
  induction 1; [constructor | constructor; assumption].
Qed.

(** The bridge: where the per-axis functions agree with their shapes,
    their sum agrees with the refinement's. *)
Lemma gsum_mdgsum (S : list nat) (gs : list (nat -> Z)) Ts (c : list nat) :
  AxisLayouts S gs Ts -> coord_ok S c -> gsum gs c = mdgsum Ts c.
Proof.
  intros HAL. revert c.
  induction HAL as [| n S g gs T Ts Hwf Ht Hn Hag HAL IH]; intros c Hc.
  - inversion Hc. reflexivity.
  - inversion Hc as [| n' S' x c' Hx Hc']; subst.
    simpl. rewrite (Hag x Hx), (IH c' Hc'). ring.
Qed.

(** ** Lemma 2, forward: a refinement forces the per-axis functions

    This is the half with the content: given that [f] IS a layout over
    some refinement, the [g_i] read off the unit coordinates are that
    refinement's per-axis digit sums. Nothing is searched for. *)
Lemma refined_axis_gs (S : list nat) (f : list nat -> Z) (k : Z) Ts :
  sizes_pos S -> Refined S Ts ->
  (forall c, coord_ok S c -> f c = k + mdgsum Ts c) ->
  AxisLayouts S (axis_gs S f) Ts.
Proof.
  revert f k Ts.
  induction S as [| n S IH]; intros f k Ts Hp HR Hf.
  - inversion HR. constructor.
  - inversion HR as [| n' S' T Ts' Hwf Ht Hn HR' Heq1 Heq2]; subst.
    assert (Hp' : sizes_pos S) by (eapply sizes_pos_tail; exact Hp).
    assert (Hoc : coord_ok S (origin S)) by (apply coord_ok_origin; exact Hp').
    assert (Hmz : mdgsum Ts' (origin S) = 0) by (apply mdgsum_origin; exact HR').
    simpl. constructor; try assumption; try reflexivity.
    + (* the head axis function IS this axis's digit sum *)
      intros v Hv.
      rewrite (Hf (v :: origin S)) by (constructor; assumption).
      rewrite (Hf (0%nat :: origin S))
        by (constructor; [pose proof (sizes_pos_head _ _ Hp); lia | assumption]).
      simpl. rewrite dgsum_zero, Hmz. ring.
    + (* and the rest is the same statement one axis along *)
      apply (IH (fun c => f (0%nat :: c)) k Ts' Hp' HR').
      intros c Hc.
      rewrite (Hf (0%nat :: c))
        by (constructor; [pose proof (sizes_pos_head _ _ Hp); lia | assumption]).
      simpl. rewrite dgsum_zero. ring.
Qed.

(** ** Lemma 2 *)

Theorem separable_iff (S : list nat) (f : list nat -> Z) :
  sizes_pos S ->
  IsRefined S f <-> (Separable S f /\ AxisLayoutsEx S (axis_gs S f)).
Proof.
  intros Hp. split.
  - intros HIR.
    destruct HIR as [k [Ts [HR Hf]]].
    assert (HAL : AxisLayouts S (axis_gs S f) Ts)
      by (eapply refined_axis_gs; eassumption).
    split; [| exists Ts; exact HAL].
    intros c Hc.
    assert (Hoc : coord_ok S (origin S)) by (apply coord_ok_origin; exact Hp).
    rewrite (Hf c Hc), (Hf (origin S) Hoc).
    rewrite (mdgsum_origin S Ts HR).
    rewrite (gsum_mdgsum S (axis_gs S f) Ts c HAL Hc). ring.
  - intros [Hsep [Ts HAL]].
    exists (f (origin S)), Ts. split; [eapply Refined_of_AxisLayouts; exact HAL |].
    intros c Hc.
    rewrite (Hsep c Hc).
    rewrite (gsum_mdgsum S (axis_gs S f) Ts c HAL Hc). reflexivity.
Qed.
