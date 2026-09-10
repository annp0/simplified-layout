(** An XOR swizzle: the [bits]-wide bit field at position [src] XORed
    into the field at position [dst]:

      eval { bits; src; dst } x
        = x lxor (((x lsr src) land (2^bits - 1)) lsl dst)

    This is the generatable non-linear family — one bitwise op on the
    address path. Bank-conflict swizzles are [dst = 0] instances.

    The two fields MUST be disjoint ([validate], enforced when a
    swizzle is attached to a layout): disjointness makes every swizzle
    an involution, hence injective, so a swizzled layout has exactly
    the collision classes of its unswizzled layout. An
    overlapping-field map (e.g. [{bits=1; src=0; dst=0}], which clears
    the low bit) is non-injective and would silently merge addresses —
    a valid-but-unmeant value class, excluded by construction. *)
type t =
  { bits : int
  ; src : int
  ; dst : int
  }
[@@deriving sexp_of, compare]

(** Raises unless [bits >= 1], [src, dst >= 0], and the fields
    [src, src+bits) and [dst, dst+bits) are disjoint. *)
val validate : t -> unit

val eval : t -> int -> int
