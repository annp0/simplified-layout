(** A layout: either a LAYOUT PROPER --- strides with an optional XOR
    swizzle, closed-form address arithmetic by construction --- or a
    COMPOSITION of two layouts, kept as the pair. A layout is a pure,
    origin-preserving access pattern; where data sits in a buffer is a
    pointer's job, not a layout's. There is deliberately no constructor
    from an arbitrary function.

    ['dom] and ['cod] are phantom space tags (see [Space]): a storage
    layout is a [(Space.logical, Space.physical) t], a thread-value
    layout a [(Space.thread_value, Space.logical) t], and the two cannot
    be confused. *)
type ('dom, 'cod) t

(** A layout between the two naming spaces, logical or thread-value on
    both sides. A physical codomain is not reachable here --- see [storage],
    which is the only constructor for one. *)
val of_linear : Linear.t -> ([< Space.source ], [< Space.source ]) t

(** The only way to build a physical-codomain layout, and its domain is
    logical. Nobody writes a thread-value map straight to addresses:
    a thread reaches memory by composing its map into logical space
    with the storage map, so the two halves stay separable and the
    thread-value map can be reused against different storage. *)
val storage : Linear.t -> (Space.logical, Space.physical) t
val shape : (_, _) t -> Shape.t
val offset : (_, _) t -> Coord.t -> int

(** Composition through a logical intermediate --- the only composition
    there is. It asks only that the operands be COMPOSABLE, in the sense
    the word already has for maps: the codomain of [f] is the domain of
    [g]. Concretely [f] must be a bijection onto [g]'s domain (sizes
    agree and [f] is dense; decided by the sorted-stride criterion for
    plain layouts, by enumeration otherwise).
    The result IS the pair: evaluation runs [f], decodes through [g]'s
    domain, runs [g]. Nothing else is computed and nothing can fail
    beyond the gate. A physical-codomain layout can never be an
    intermediate: no signature accepts one on the left. *)
val compose : ('a, Space.logical) t -> (Space.logical, 'c) t -> ('a, 'c) t

(** Post-compose an XOR swizzle onto a layout (raises on a composite).
    Physical codomain only, by type: logical spaces are canonical by
    definition. Raises if a swizzle is already set. *)
val with_swizzle
  :  (Space.logical, Space.physical) t
  -> Swizzle.t
  -> (Space.logical, Space.physical) t

(** Structural operations, on layouts (raise on composites --- they
    build storage and thread maps, which are layouts; a composite is a
    finished address map). See [Linear] for their semantics. *)

val divide : by:Shape.t -> ('dom, 'cod) t -> ('dom, 'cod) t
val repeat : by:Linear.t -> ('dom, 'cod) t -> ('dom, 'cod) t
val interleave : by:Linear.t -> ('dom, 'cod) t -> ('dom, 'cod) t
val broadcast
  :  by:Shape.t
  -> (Space.logical, Space.physical) t
  -> (Space.logical, Space.physical) t

(** Inverse of a dense logical-codomain layout, with the spaces swapped:
    the inverse of a thread-value map [(tv, logical)] is the ownership
    map [(logical, tv)]. See [Linear.inverse].

    Layouts only, and that is not an oversight: every layout left of
    physical is a bijection, so an inverse FUNCTION always exists, but
    bijectivity buys a function and not a presentation --- a composite's
    inverse need not be a layout at all. [Decide.strided_form] is what
    answers that, for any map. *)
val inverse : ('dom, Space.logical) t -> (Space.logical, 'dom) t

(** The two validity checks, by enumeration (the density check uses the
    sorted-stride criterion when the layout has no swizzle). O(size),
    run once at kernel-compilation time. *)

val is_injective : (_, _) t -> bool

(** Two coordinates share an offset only if they are declared replicas:
    for a layout, they differ solely in [Broadcast] slots; for a
    composition, evaluating the first map and decoding through the
    second's domain sends them to declared replicas of the second
    (recursively). Declared replication is thus inherited by composites
    from the storage they address. The physical-side validity
    requirement; store targets additionally need [is_injective]. *)
val is_alias_free : (_, _) t -> bool

val is_bijection_onto : (_, _) t -> size:int -> bool

(** The address expression over the coordinate variables (named by
    tree path), as the composition pipeline: a layout is its affine sum
    under its swizzle, and a composition binds each stage's index and
    reads the next stage's digits off it. Total, and closed-form for
    every layout. *)
val expr : (_, _) t -> Expr.t

(** The map as a strided form over a refinement of the domain when one
    exists, and [None] --- a proof that none exists --- when not. See
    [Decide]; costs [O(size)] evaluations. *)
val strided_form : (_, _) t -> Expr.t option

(** The generated per-lane address arithmetic: [strided_form] when the
    map has one, the pipeline otherwise. *)
val to_expr : (_, _) t -> string
