
module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val eqb : int -> int -> bool

  val max : int -> int -> int
 end

val append : char list -> char list -> char list

val length : char list -> int

type set = int -> bool

val emptySet : set

val updateSet : set -> int -> set

type eExp =
| ENum of int
| EStr of char list
| EId of int
| EPlus of eExp * eExp
| ETimes of eExp * eExp
| ECat of eExp * eExp
| ELen of eExp
| ELet of eExp * int * eExp

val get_fresh_var : eExp -> int

val fresh_rename : eExp -> set -> int -> eExp

val subst' : eExp -> int -> eExp -> eExp

val subst : eExp -> int -> eExp -> eExp

val is_val : eExp -> bool

val eval : eExp -> eExp option

val eval_big : eExp -> eExp option
