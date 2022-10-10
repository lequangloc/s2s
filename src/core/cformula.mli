open Globals
open Gen.Basic
open VarGen

module CB = Csymheap
module CP = Cpure

type formula =
  | Base of CB.formula
  | Exists of (CB.formula * (Var.t list))
  | Or of (formula * formula* loc)


type t = formula

val string_of: t -> string

val mkTrue : loc -> t

val mkFalse : loc -> t

val isFalse : t -> bool

val mkBase : Cheap.t -> Cpure.t -> loc -> t

val mkExists : Var.t list -> Cheap.t ->  Cpure.t -> loc -> t

val mkOr : t -> t -> loc -> t

val mkStarAnd : ?avoid_clash:bool -> t -> t -> t

val mkPureAnd : t -> CP.t -> t

val isEmptyHeap : t -> bool
val isHTrueHeap : t -> bool

val is_empty_true : t -> bool

(* without disjunction *)
val add_quantifiers : Var.t list -> t -> t

val split_quantifiers : t -> (Var.t list * t)

val push_exists : Var.t list -> t -> t

val simplify_pure : t -> t

val fresh_quantifiers : t -> t

val subst : (Var.t * Var.t) list -> t -> t

val subst_view_inv : (String.t * (Var.t list * CP.t)) list -> t -> t

val fv : t -> Var.t list

val contain_pred : t -> string -> bool

val subtract_pto : t -> CptoNode.t -> t

val subtract_pred : t -> CpredNode.t -> t

val subtract_useless_diseq : t -> Var.t list -> t

val list_of_disjuncts : t -> t list

val to_disjunct_form: t list -> t

val sequentialize_views : t -> t

val subst_type : (typ * typ) list -> t -> t

val star_decompose : t -> (CpredNode.t list) * (CptoNode.t list)

val decompose : t -> Var.t list * (CpredNode.t list) * (CptoNode.t list) * Cpure.t

val update_view_unfold_number: int -> t -> t

val increase_view_unfold_number: t -> t

val is_pure_top : t -> bool

val remove_redundant : t -> bool * t
(*
  apply after unfolding may help to remove some redundant
  remove redundant pure formula
  if it is unsat return true, othrwise false
*)

(*
two formula is only syntactically similar after substi ex. qvars
*)
val equal : t -> t -> bool

val remove_dups : t -> t
