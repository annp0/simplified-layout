open! Base

let leaves shape =
  let rec go path (s : Shape.t) acc =
    match s with
    | Bound n -> (path, n) :: acc
    | Product ss -> List.foldi ss ~init:acc ~f:(fun j acc s -> go (path @ [ j ]) s acc)
  in
  List.rev (go [] shape [])
;;

let coord_of shape ~assign =
  let rec go path (s : Shape.t) : Coord.t =
    match s with
    | Bound _ -> Idx (assign path)
    | Product ss -> Tuple (List.mapi ss ~f:(fun j s -> go (path @ [ j ]) s))
  in
  go [] shape
;;

let indices_of c =
  let rec go path (c : Coord.t) acc =
    match c with
    | Idx i -> (path, i) :: acc
    | Tuple cs -> List.foldi cs ~init:acc ~f:(fun j acc c -> go (path @ [ j ]) c acc)
  in
  go [] c []
;;

(* PER-AXIS RECOGNIZER, linear time.

   A digit satisfies [(v / w) mod r = (v / w) - r * (v / (w*r))], so
   every strided form of [g] is equally a weighted sum of floor terms
   [sum_w c_w * (v / w)] over a chain of divisors of [n]. First
   differences turn [v / w] into the indicator of the multiples of [w]:
   with [h t = g t - g (t-1)],
     [h t = sum_w c_w * (if w divides t then 1 else 0)].
   Scanning [t] upwards, the first [t] with [h t <> 0] must be a weight
   and its coefficient is forced to be [h t], since every smaller weight
   has already had its contribution subtracted off. Subtracting it from
   the multiples of [t] repeats the argument.

   A strided form exists exactly when the weights so forced divide [n]
   and form a divisibility chain, which is what the two rejections test.
   Those weights are moreover NECESSARY boundaries, so together with
   weight 1 --- which every refinement carries, since the digits must
   cover the axis --- they are the weights of the COARSEST refinement,
   not merely the coefficients of some chosen one. Weight 1 is therefore
   returned whatever its coefficient: for [g v = v / 2] on [n = 4] the
   scan reports only weight 2, but the refinement is [(2, 2)] with
   strides [(0, 1)], and dropping its first digit would leave radices
   whose product is not [n]. A constant [g] (necessarily zero, since
   [g 0 = 0]) returns the trivial refinement, one digit of radix [n] at
   stride 0; [n = 1] returns no digits at all.

   Each accepted weight is a strictly larger multiple of the previous,
   so weights at least double and the subtraction loops run fewer than
   [n + n/2 + n/4 + ... < 2n] times: linear, with no factorization and
   no search over orderings. *)
let fit_axis g ~n =
  if n = 1
  then Some []
  else (
    let h = Array.init n ~f:(fun t -> if t = 0 then 0 else g t - g (t - 1)) in
    (* weight 1 always: a refinement's digits must cover the axis *)
    let boundaries = ref [ 1 ] in
    let last = ref 1 in
    let rejected = ref false in
    let w = ref 1 in
    while (not !rejected) && !w < n do
      let a = h.(!w) in
      if a <> 0
      then
        if n % !w <> 0 || !w % !last <> 0
        then rejected := true
        else (
          if !w > 1 then boundaries := !w :: !boundaries;
          last := !w;
          let t = ref !w in
          while !t < n do
            h.(!t) <- h.(!t) - a;
            t := !t + !w
          done);
      Int.incr w
    done;
    if !rejected
    then None
    else (
      let rec pairs = function
        | [] -> []
        | [ w ] -> [ w, n ]
        | w :: (next :: _ as rest) -> (w, next) :: pairs rest
      in
      (* (radix, weight, price) for each boundary, coarsest by
         construction; the last runs to [n], so its modulus is vacuous *)
      Some
        (List.rev_map (pairs (List.rev !boundaries)) ~f:(fun (w, next) ->
           next / w, w, g w)
         |> List.rev)))
;;

let strided_form ~shape ~offset =
  let ls = leaves shape in
  let k = offset (coord_of shape ~assign:(fun _ -> 0)) in
  let gs =
    List.map ls ~f:(fun (path, n) ->
      ( path
      , n
      , Array.init n ~f:(fun v ->
          offset
            (coord_of shape ~assign:(fun p -> if List.equal ( = ) p path then v else 0))
          - k) ))
  in
  let separable =
    List.for_all (Coord.enumerate shape) ~f:(fun c ->
      let ix = indices_of c in
      let want =
        List.fold gs ~init:k ~f:(fun acc (path, _, g) ->
          acc + g.(List.Assoc.find_exn ix path ~equal:(List.equal ( = ))))
      in
      offset c = want)
  in
  if not separable
  then None
  else (
    let per_axis =
      List.map gs ~f:(fun (path, n, g) ->
        if n = 1
        then Some (path, n, [])
        else Option.map (fit_axis (fun v -> g.(v)) ~n) ~f:(fun ds -> path, n, ds))
    in
    if List.exists per_axis ~f:Option.is_none
    then None
    else
      Some
        (Expr.add
           (Expr.Const k)
           (Expr.sum
              (List.map (List.filter_opt per_axis) ~f:(fun (path, n, ds) ->
                 let c = Expr.var (Linear.var_name path) in
                 Expr.sum
                   (List.map ds ~f:(fun (r, w, s) ->
                      let scaled = Expr.div c w in
                      let digit = if w * r = n then scaled else Expr.modulo scaled r in
                      Expr.scale s digit)))))))
;;
