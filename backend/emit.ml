(* From an address expression to SASS.

   The expressions come from the layout algebra: a composite's strided form, or
   its pipeline with the compile-time coordinates pinned. The emitter chooses
   instructions and never decides what an address is. It knows the range of
   every variable, so it drops a division or a modulus the range makes exact --
   (32 l + 4 q) / 32 is l when 4 q < 32 -- and a subexpression it has emitted
   once is reused, not recomputed. *)

open Layouts

let pow2 n = n > 0 && n land (n - 1) = 0

let rec log2 n = if n <= 1 then 0 else 1 + log2 (n / 2)

let fdiv a b =
  let q = a / b in
  if a mod b <> 0 && (a < 0) <> (b < 0) then q - 1 else q

(* a 32-bit immediate, as the instruction reads it *)
let imm32 k = k land 0xffffffff

(* The smallest shift whose reciprocal divides exactly over [0, bound): the
   divisor is known at compile time, so this is a search, not an
   approximation, and it fails rather than round. *)
let exact_recip d bound =
  let rec search sh =
    if sh > 30
    then failwith "Emit: no exact reciprocal"
    else (
      let m = ((1 lsl sh) / d) + 1 in
      let rec ok t = t >= bound || ((t * m) lsr sh = t / d && ok (t + 1)) in
      if m * (bound - 1) < 0x40000000 && ok 0 then m, sh else search (sh + 1))
  in
  search 1

let affine (e : Expr.t) =
  match e with
  | Const c -> [], c
  | Sum (ts, c) -> ts, c
  | e -> [ 1, e ], 0

let of_terms ts c = Expr.add (Expr.sum (List.map (fun (a, t) -> Expr.scale a t) ts)) (Const c)

(* the expression with its bindings substituted: sharing is recovered by the
   memo table, which sees the substituted copies as the same subexpression *)
let rec inline env (e : Expr.t) : Expr.t =
  match e with
  | Const _ -> e
  | Var v -> (match List.assoc_opt v env with Some x -> x | None -> e)
  | Sum (ts, c) -> of_terms (List.map (fun (a, t) -> a, inline env t) ts) c
  | Div (x, w) -> Expr.div (inline env x) w
  | Mod (x, r) -> Expr.modulo (inline env x) r
  | Xor (a, b) -> Expr.xor (inline env a) (inline env b)
  | Let (x, e1, body) -> inline ((x, inline env e1) :: env) body

(* inclusive bounds of a value, by interval arithmetic over the variables'
   ranges ([range v] values: 0 .. range v - 1) *)
let rec bounds range (e : Expr.t) =
  match e with
  | Const c -> c, c
  | Var v -> 0, range v - 1
  | Sum (ts, c) ->
    List.fold_left
      (fun (lo, hi) (a, t) ->
        let l, h = bounds range t in
        if a >= 0 then lo + (a * l), hi + (a * h) else lo + (a * h), hi + (a * l))
      (c, c)
      ts
  | Div (x, w) ->
    let l, h = bounds range x in
    fdiv l w, fdiv h w
  | Mod (x, r) ->
    let l, h = bounds range x in
    if l >= 0 && h < r then l, h else 0, r - 1
  | Xor (a, b) ->
    let la, ha = bounds range a
    and lb, hb = bounds range b in
    if la < 0 || lb < 0 then failwith "Emit: exclusive-or of a signed value";
    let rec up p = if p > max ha hb then p else up (2 * p) in
    0, up 1 - 1
  | Let _ -> failwith "Emit.bounds: inline the bindings first"

(* A division or modulus by w of [whole + part], where w divides every
   coefficient of [whole], reads only [whole] when [part] lies in [0, w): the
   rewrite is exact over the ranges, not a guess. *)
let rec simplify range (e : Expr.t) : Expr.t =
  match e with
  | Const _ | Var _ -> e
  | Sum (ts, c) -> of_terms (List.map (fun (a, t) -> a, simplify range t) ts) c
  | Div (x, w) ->
    let x = simplify range x in
    let ts, c = affine x in
    let whole, part = List.partition (fun (a, _) -> a mod w = 0) ts in
    let pl, ph = bounds range (of_terms part c) in
    if pl >= 0 && ph < w then of_terms (List.map (fun (a, t) -> a / w, t) whole) 0 else Expr.div x w
  | Mod (x, r) ->
    let x = simplify range x in
    let ts, c = affine x in
    let _, part = List.partition (fun (a, _) -> a mod r = 0) ts in
    let rest = of_terms part c in
    let pl, ph = bounds range rest in
    if pl >= 0 && ph < r then rest else Expr.modulo x r
  | Xor (a, b) -> Expr.xor (simplify range a) (simplify range b)
  | Let _ -> failwith "Emit.simplify: inline the bindings first"

type operand =
  | Reg of int
  | Imm of int

type t =
  { b : Sass.t
  ; mutable free : int list
  ; memo : (Expr.t, operand) Hashtbl.t
  ; mutable high : int
  }

(* one emission site: scratch registers are handed out from [scratch] and are
   dead once the site's results have been read *)
let create b ~scratch = { b; free = scratch; memo = Hashtbl.create 16; high = -1 }

let fresh t =
  match t.free with
  | r :: rest ->
    t.free <- rest;
    t.high <- max t.high r;
    r
  | [] -> failwith "Emit: out of scratch registers"

let to_reg t = function
  | Reg r -> r
  | Imm k ->
    let d = fresh t in
    Sass.mov_imm t.b d (imm32 k);
    d

let rec emit t ~range ~reg (e : Expr.t) : operand =
  match Hashtbl.find_opt t.memo e with
  | Some o -> o
  | None ->
    let o =
      match e with
      | Const c -> Imm c
      | Var v -> Reg (reg v)
      | Sum (ts, c) -> emit_sum t ~range ~reg ts c
      | Div (x, w) ->
        let rx = to_reg t (emit t ~range ~reg x) in
        let d = fresh t in
        if pow2 w
        then Sass.shf_r t.b d rx (log2 w)
        else (
          let lo, hi = bounds range x in
          if lo < 0 then failwith "Emit: division of a signed value";
          let m, sh = exact_recip w (hi + 1) in
          Sass.imad_rz t.b d rx m;
          Sass.shf_r t.b d d sh);
        Reg d
      | Mod (x, r) ->
        let rx = to_reg t (emit t ~range ~reg x) in
        let d = fresh t in
        if pow2 r
        then Sass.lop3_and t.b d rx (r - 1)
        else (
          let q = to_reg t (emit t ~range ~reg (Expr.div x r)) in
          Sass.imad t.b d q (imm32 (-r)) rx);
        Reg d
      | Xor (a, b) ->
        let oa = emit t ~range ~reg a
        and ob = emit t ~range ~reg b in
        let d = fresh t in
        (match oa, ob with
         | Reg ra, Reg rb -> Sass.lop3_xor t.b d ra rb
         | Reg ra, Imm k | Imm k, Reg ra -> Sass.lop3_xor_imm t.b d ra (imm32 k)
         | Imm x, Imm y -> Sass.mov_imm t.b d (imm32 (x lxor y)));
        Reg d
      | Let _ -> failwith "Emit.emit: inline the bindings first"
    in
    Hashtbl.replace t.memo e o;
    o

(* a sum: each scaled term is its own subexpression, so a term every address
   of a site shares is computed once *)
and emit_sum t ~range ~reg ts c =
  let scaled (a, term) =
    let key = Expr.Sum ([ a, term ], 0) in
    match Hashtbl.find_opt t.memo key with
    | Some o -> o
    | None ->
      let o =
        match emit t ~range ~reg term with
        | Imm k -> Imm (a * k)
        | Reg r when a = 1 -> Reg r
        | Reg r ->
          let d = fresh t in
          Sass.imad_rz t.b d r (imm32 a);
          Reg d
      in
      Hashtbl.replace t.memo key o;
      o
  in
  let acc, k =
    List.fold_left
      (fun (acc, k) term ->
        match scaled term, acc with
        | Imm x, _ -> acc, k + x
        | Reg r, None -> Some r, k
        | Reg r, Some a ->
          let d = fresh t in
          Sass.iadd3 t.b d a r;
          Some d, k)
      (None, c)
      ts
  in
  match acc with
  | None -> Imm k
  | Some a when k = 0 -> Reg a
  | Some a ->
    let d = fresh t in
    Sass.iadd3_c t.b d a (imm32 k);
    Reg d

(* the value of [e] in register [dst]; [range] bounds every variable, [reg]
   names the register holding it *)
let into t ~range ~reg e ~dst =
  let e = simplify range (inline [] e) in
  match emit t ~range ~reg e with
  | Reg r when r = dst -> ()
  | Reg r -> Sass.mov_rr t.b dst r
  | Imm k -> Sass.mov_imm t.b dst (imm32 k)
