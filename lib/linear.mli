(** Strided layouts: the concrete, data-representable subset of layouts.
    The map is [sum over leaves], so it is plain data that operations
    can manipulate. Two leaf kinds, one meaning each:

      Axis  {size; stride}   n points, distinct addresses (i * stride)
      Broadcast {size}       n points, one address (contributes 0)

    [Broadcast] is replication, legal only in physical-codomain layouts;
    on the logical side [compose]'s density gate rejects it — it is
    non-injective. *)
type t =
  | Axis of
      { size : int
      ; stride : int
      }
  | Broadcast of { size : int }
  | Group of t list
[@@deriving sexp_of, compare]

(** Domain of the constructors: sizes >= 1, strides >= 1. Enforced at
    construction because ops multiply strides — a malformed value would
    propagate before any semantic check runs. *)
val validate : t -> unit

val shape : t -> Shape.t
val eval : t -> Coord.t -> int

(** The row-major layout of [shape]: last axis fastest, innermost
    stride 1. Always a bijection onto [0, Shape.size shape).
    [Coord.unflatten] is its inverse. *)
val canonical : Shape.t -> t

(** Footprint: one past the largest offset the layout can produce.
    Equals [Shape.size (shape t)] exactly when the layout is dense;
    strictly greater when the image has holes (padding). *)
val cosize : t -> int

(** [split ~by t] regroups a single axis into the shape [by]
    ([Shape.size by] must equal the axis size): the index is
    reinterpreted as a [by]-coordinate, row-major. The underlying map —
    and hence density — is unchanged. Two-way partition is
    [~by:(Product [Bound (n/k); Bound k])]. Splitting a [Broadcast]
    yields a broadcast tree. *)
val split : by:Shape.t -> t -> t

(** Coordinate variable name for a tree path: [c], [c0], [c1_0], ... *)
val var_name : int list -> string

(** THE partition — CuTe's zipped_divide with a shape tiler.
    [divide ~by t] chops [t] into [by]-shaped tiles: per axis, size n_i
    splits into (n_i / k_i, k_i), and the pieces regroup as

      Group [ tile axes ; rest axes ]

    coordinate ((tile coords), (which tile)). The underlying map — and
    hence density — is unchanged: it is a bijective relabeling that
    KEEPS every tile ([rest] is the complement, carried by
    construction). Picking one tile is [Restricted.restrict] on the
    rest coords, afterwards. [by] must be congruent with [shape t] and
    divide it per axis; raises otherwise. Strided tilers (tiles from
    non-adjacent elements) are not offered until a caller exists. *)
val divide : by:Shape.t -> t -> t

(** [repeat ~by t]: copies of [t] arranged by [by], a DENSE layout
    (checked) whose strides are in units of [cosize t] and say only the
    ORDER of the copies — n in a row, a row-major grid, a column-major
    grid. Padding never lives in the arrangement: pad the tile itself
    (its cosize then spaces the copies), or write the group directly
    for an arbitrary stride. Copies at DISTINCT addresses: the dual of
    [broadcast]. *)
val repeat : by:t -> t -> t

(** [broadcast ~by t]: copies of [t] all at the SAME addresses. The
    copy axes have sizes but no strides to give, hence [by] is a
    [Shape.t]. The dual of [repeat]. *)
val broadcast : by:Shape.t -> t -> t

(** [interleave ~by t]: copies of [t] interleaved element-wise (CuTe's
    logical_product with the copies as the first operand) — the mirror
    of [repeat]: the copies keep their
    strides in element units and the TILE's strides are dilated by the
    cell size. [repeat] lays tiles side by side; [interleave] deals
    them out like cards. [by] is a DENSE arrangement (checked, same rule
    as [repeat]): its strides are the copies' positions within the
    interleave cell, and the cell is exactly packed. *)
val interleave : by:t -> t -> t

(** Exact density check, no enumeration: by the running-product
    characterization, a strided layout is a bijection onto [0, size)
    iff it has no [Broadcast] (of size > 1), its sizes multiply to
    [size], and its stride-sorted axes satisfy s(1) = 1 and
    s(j+1) = s(j) * n(j). O(k log k) in the number of axes. *)
val is_dense : t -> size:int -> bool

(** Inverse of a DENSE layout, as a layout: index j |-> the canonical
    index (in [t]'s domain) of the coordinate that [t] sends to j. The
    law: [eval (inverse t) (unflatten (shape (inverse t)) (eval t c))]
    is the canonical index of [c]. CuTe's [right_inverse] on the dense
    fragment; for a thread-value map it is the OWNERSHIP map, "which
    thread and value hold this element". Raises unless dense. *)
val inverse : t -> t

