open Globals
open Gen.Basic
open VarGen


module CP = Cpure
module CH = Cheap

type formula = {
  base_heap : CH.formula;
  base_pure : CP.formula;
  base_pos : loc }

type t = formula

val string_of: t -> string

val mk :  Cheap.t -> Cpure.t -> loc -> t

val mkTrue : loc -> t

val mkFalse : loc -> t

val isFalse : t -> bool

val mkStarAnd : t -> t -> t

val subtract_pto : t -> CptoNode.t -> t

val subtract_pred : t -> CpredNode.t -> t

val subst : (Var.t * Var.t) list -> t -> t

val subst_view_inv: (String.t * (Var.t list * CP.t)) list -> t -> t

val fv : t -> Var.t list

val sequentialize_views : t -> t

val subst_type : (typ * typ) list -> t -> t

val equal : t -> t -> bool
