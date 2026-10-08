
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

val sub : nat -> nat -> nat

module Nat :
 sig
  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val eqb : positive -> positive -> bool

  val of_succ_nat : nat -> positive
 end

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val eqb : z -> z -> bool

  val of_nat : nat -> z
 end

val divides_ind : nat -> nat -> z

val dsum : (nat, z) prod list -> nat -> z

val resid : (nat -> z) -> (nat, z) prod list -> nat -> z

val scan_from :
  nat -> (nat -> z) -> nat -> nat -> nat -> (nat, z) prod list -> (nat, z)
  prod list option

val first_diff : (nat -> z) -> nat -> z

val scan : nat -> (nat -> z) -> (nat, z) prod list option

val next_w : nat -> (nat, z) prod list -> nat

val shape_of :
  nat -> z -> (nat, z) prod list -> ((nat, nat) prod, z) prod list

val with_one : (nat, z) prod list -> (nat, z) prod list

val shape_of_chain :
  nat -> (nat, z) prod list -> ((nat, nat) prod, z) prod list
