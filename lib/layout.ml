open! Base

type ('dom, 'cod) t =
  | Atom :
      { linear : Linear.t
      ; swizzle : Swizzle.t option
      }
      -> ('dom, 'cod) t
  | Seq : ('dom, 'mid) t * ('mid, 'cod) t -> ('dom, 'cod) t

let of_linear linear =
  Linear.validate linear;
  Atom { linear; swizzle = None }
;;

let storage linear =
  Linear.validate linear;
  Atom { linear; swizzle = None }
;;

let rec shape : type a b. (a, b) t -> Shape.t = function
  | Atom { linear; _ } -> Linear.shape linear
  | Seq (f, _) -> shape f
;;

let rec offset : type a b. (a, b) t -> Coord.t -> int =
  fun t c ->
  match t with
  | Atom { linear; swizzle } ->
    let off = Linear.eval linear c in
    (match swizzle with
     | None -> off
     | Some sw -> Swizzle.eval sw off)
  | Seq (f, g) -> offset g (Coord.unflatten (shape g) (offset f c))
;;

let atom_exn : type a b. op:string -> (a, b) t -> Linear.t * Swizzle.t option =
  fun ~op t ->
  match t with
  | Atom { linear; swizzle } -> linear, swizzle
  | Seq _ ->
    let msg =
      op
      ^ ": defined on atoms; a composition's components are the operands the caller \
         already holds"
    in
    raise_s (Sexp.Atom msg)
;;


let with_swizzle t sw =
  Swizzle.validate sw;
  match atom_exn ~op:"Layout.with_swizzle" t with
  | _, Some _ -> raise_s [%message "Layout.with_swizzle: layout already has a swizzle"]
  | linear, None -> Atom { linear; swizzle = Some sw }
;;

let divide ~by t =
  let linear, swizzle = atom_exn ~op:"Layout.divide" t in
  Atom { linear = Linear.divide ~by linear; swizzle }
;;

(* Multiples of a power-of-two [granularity] commute with [sw] exactly
   when both its bit fields sit below it: the multiples contribute no
   bits the swizzle reads or writes. *)
let fields_below (sw : Swizzle.t) ~granularity =
  Int.is_pow2 granularity
  &&
  let k = Int.floor_log2 granularity in
  sw.src + sw.bits <= k && sw.dst + sw.bits <= k
;;

let repeat ~by t =
  let lin, swizzle = atom_exn ~op:"Layout.repeat" t in
  let linear = Linear.repeat ~by lin in
  match swizzle with
  | None -> Atom { linear; swizzle }
  | Some sw ->
    let footprint = Linear.cosize lin in
    if fields_below sw ~granularity:footprint
    then Atom { linear; swizzle }
    else
      raise_s
        [%message
          "Layout.repeat: the swizzle reads bits at or above the copy stride, so the \
           copies would not be independently swizzled"
            (sw : Swizzle.t)
            (footprint : int)]
;;

let broadcast ~by t =
  let linear, swizzle = atom_exn ~op:"Layout.broadcast" t in
  Atom { linear = Linear.broadcast ~by linear; swizzle }
;;

let interleave ~by t =
  match atom_exn ~op:"Layout.interleave" t with
  | linear, None -> Atom { linear = Linear.interleave ~by linear; swizzle = None }
  | _, Some _ ->
    raise_s
      [%message
        "Layout.interleave: no meaning is defined for interleaving a swizzled layout \
         (no known kernel pattern needs it)"]
;;

let inverse t =
  let linear, _ = atom_exn ~op:"Layout.inverse" t in
  Atom { linear = Linear.inverse linear; swizzle = None }
;;

let image t = List.map (Coord.enumerate (shape t)) ~f:(offset t)

let is_injective t =
  let img = image t in
  List.length (List.dedup_and_sort img ~compare:Int.compare) = List.length img
;;

(* Zero every Broadcast slot of an atom's coordinate: coordinates that
   then coincide are the atom's declared-replication classes. *)
let rec mask_broadcast (l : Linear.t) (c : Coord.t) : Coord.t =
  match l, c with
  | Broadcast _, Idx _ -> Idx 0
  | Group ts, Tuple cs -> Tuple (List.map2_exn ts cs ~f:mask_broadcast)
  | _, c -> c
;;

(* The declared-replication class of a coordinate. For an atom: the
   coordinate with its Broadcast slots zeroed. For a composition: the
   class, in the second map, of the decoded image under the first ---
   declared replication is inherited from the storage the composite
   addresses, even though the composite's own domain has no Broadcast
   slots. Since the first map is a bijection onto the second's domain,
   composition preserves the second's declared aliasing and adds none. *)
let rec replica_key : type a b. (a, b) t -> Coord.t -> Coord.t =
  fun t c ->
  match t with
  | Atom { linear; _ } -> mask_broadcast linear c
  | Seq (f, g) -> replica_key g (Coord.unflatten (shape g) (offset f c))
;;

let is_alias_free t =
  let classes =
    List.map (Coord.enumerate (shape t)) ~f:(fun c -> replica_key t c, offset t c)
    |> List.dedup_and_sort ~compare:(fun (k, _) (k', _) -> Coord.compare k k')
  in
  let offsets = List.map classes ~f:snd in
  List.length (List.dedup_and_sort offsets ~compare:Int.compare) = List.length classes
;;

let is_bijection_onto t ~size =
  match t with
  (* plain atom: decided exactly by the running-product characterization *)
  | Atom { linear; swizzle = None } -> Linear.is_dense linear ~size
  | _ ->
    let sorted = List.sort (image t) ~compare:Int.compare in
    List.equal Int.equal sorted (List.init size ~f:Fn.id)
;;

let compose f g =
  if not (is_bijection_onto f ~size:(Shape.size (shape g)))
  then
    raise_s
      [%message
        "Layout.compose: the left operand is not a bijection onto the domain of the \
         right"
          ~left:(shape f : Shape.t)
          ~right:(shape g : Shape.t)];
  Seq (f, g)
;;

(* --- expression emission ---

   Two forms and nothing else. If the map has a strided form over a
   refinement of its domain, [Decide] returns it; that is complete, so
   nothing is left for a rewrite system to find. Otherwise the pipeline
   is written out with one binding per stage: the stage's index is
   computed once and its digits are read off it, which is smaller than
   any inlined rewriting of it. *)

let vars_expr linear =
  let rec go path = function
    | Linear.Axis { size = 1; _ } | Broadcast _ -> Expr.Const 0
    | Axis { size = _; stride } -> Expr.scale stride (Expr.var (Linear.var_name path))
    | Group ts -> Expr.sum (List.mapi ts ~f:(fun i t -> go (path @ [ i ]) t))
  in
  go [] linear
;;

(* an atom applied to a stage index: decode each digit (division by its
   weight, modulus by its radix) and price it *)
let decode_expr linear x =
  let rec axes = function
    | Linear.Axis { size; stride } -> [ Some stride, size ]
    | Broadcast { size } -> [ None, size ]
    | Group ts -> List.concat_map ts ~f:axes
  in
  let digits, _ =
    List.fold_right (axes linear) ~init:([], 1) ~f:(fun (stride, size) (acc, w) ->
      (stride, size, w) :: acc, w * size)
  in
  let n = Shape.size (Linear.shape linear) in
  (* an atom whose strides are the canonical weights is the identity on
     the index: decoding and repricing it returns what it was given *)
  if List.for_all digits ~f:(fun (stride, size, w) ->
       size = 1 || Option.equal ( = ) stride (Some w))
  then x
  else
    Expr.sum
    (List.filter_map digits ~f:(fun (stride, size, w) ->
       match stride with
       | None -> None
       | Some _ when size = 1 -> None
       | Some s ->
         (* the leading digit needs no modulus: [x < n] is the
            composability of the pair, so [x / w < size] *)
         let scaled = Expr.div x w in
         let digit = if w * size = n then scaled else Expr.modulo scaled size in
         Some (Expr.scale s digit)))
;;

(* the swizzle reads a field of the address it is given, so the address
   is bound: it is computed once, not once per use *)
let swizzle_expr ~depth swizzle e =
  match swizzle with
  | None -> e
  | Some ({ bits; src; dst } : Swizzle.t) ->
    let name = Printf.sprintf "a%d" depth in
    let a = Expr.var name in
    Expr.bind
      name
      e
      (Expr.xor a (Expr.scale (1 lsl dst) (Expr.modulo (Expr.div a (1 lsl src)) (1 lsl bits))))
;;

let rec expr_index : type a b. (a, b) t -> depth:int -> Expr.t -> Expr.t =
  fun t ~depth x ->
  match t with
  | Atom { linear; swizzle } ->
    let name = Printf.sprintf "x%d" depth in
    Expr.bind name x (swizzle_expr ~depth swizzle (decode_expr linear (Expr.var name)))
  | Seq (f, g) -> expr_index g ~depth:(depth + 1) (expr_index f ~depth x)
;;

let rec expr : type a b. (a, b) t -> Expr.t = function
  | Atom { linear; swizzle } -> swizzle_expr ~depth:0 swizzle (vars_expr linear)
  | Seq (f, g) -> expr_index g ~depth:1 (expr f)
;;

let strided_form t = Decide.strided_form ~shape:(shape t) ~offset:(offset t)

let to_expr t =
  match strided_form t with
  | Some e -> Expr.to_string e
  | None -> Expr.to_string (expr t)
;;
