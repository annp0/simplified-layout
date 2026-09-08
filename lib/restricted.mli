(** A restricted layout: an UNMODIFIED layout plus the restriction that
    fixes some of its coordinate slots. Nothing is folded or split —
    evaluation completes the coordinate (fixed slots contribute their
    [At] index) and evaluates the original map, so it is total for
    every map, layouts and composites alike, with no case analysis.

    Fixed slots keep their position with shape [Bound 1] and take the
    coordinate [Idx 0].

    Restriction is PHYSICAL-CODOMAIN ONLY: selection is an
    execution-side act (this executor touches these addresses), while
    logical space is the accounting side whose density invariant
    forbids discarding elements. Slicing happens AFTER composition:
    warp and thread coordinates live in the composite's domain, and
    pinning them there is all a slice is. *)
type ('dom, 'cod) t

val restrict
  :  at:Coord.partial
  -> ('dom, Space.physical) Layout.t
  -> ('dom, Space.physical) t

(** Further restriction: the union of the restrictions. [at] is written
    against the RESTRICTED shape, so on an already-fixed slot (shape
    [Bound 1]) it can only say [Free] or [At 0]; free slots may be
    fixed. Hierarchy slicing is repeated union: warp slice, then thread
    slice. *)
val restrict_more : at:Coord.partial -> ('dom, 'cod) t -> ('dom, 'cod) t

(** The two pieces, for inspection and codegen. *)
val layout : ('dom, 'cod) t -> ('dom, 'cod) Layout.t

val restriction : (_, _) t -> Coord.partial

(** The restricted domain: fixed slots shrink to [Bound 1]. *)
val shape : (_, _) t -> Shape.t

val offset : (_, _) t -> Coord.t -> int

(** The generated per-lane expression: [strided_form] when there is one,
    otherwise the layout's pipeline with the pinned variables replaced
    by their constants. *)
val to_expr : (_, _) t -> string
