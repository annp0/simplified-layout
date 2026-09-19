(** * Extraction

    The point of extracting is to close the gap between "we proved an
    algorithm" and "our code runs the proved algorithm". [scan] and
    [shape_of_chain] come out as OCaml and are compared with
    [Decide.fit_axis] over the whole enumeration the paper quotes --- a
    stronger check than [check.sh], which compares counts computed
    inside Coq and cannot reach the [n = 12] case.

    Extraction is FAITHFUL: no [Extract Inductive] remapping, so [nat]
    stays unary and [Z] stays Coq's binary integers. Remapping [nat] to
    OCaml's [int] is the usual trick and would be faster, but it is an
    unproved assumption about overflow, and the numbers here are axis
    sizes and strides --- small. Nothing is assumed that the proofs do
    not already establish. *)

From Coq Require Import Extraction.
From LayoutAlgebra Require Import Floors Chain Recognize Shape.

Extraction Language OCaml.

(* [Recognize.scan] decides; [Shape.shape_of_chain] turns the chain it
   returns into the shape with strides, which is what fit_axis returns. *)
Extraction "extracted/layout_scan.ml" scan shape_of_chain.
