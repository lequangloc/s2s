
open Globals
open Gen.Basic
open VarGen



type formula =
  | Star of (formula * formula * loc)
  | PtoNode of CptoNode.pto
  | PredNode of CpredNode.hpred
  | HEmp
  | HTrue
  | HFalse


and t = formula

val string_of: t -> string

val mkHTrue : loc -> t

val mkHFalse : loc -> t

val mkPtoNode: Var.t -> Var.t list -> Globals.ident -> bool -> int list -> loc -> t

val mkPredNode:  Globals.ident -> bool -> Var.t list -> loc -> t

val mkStarAnd: t -> t -> loc -> t

val h_subst: (Var.t * Var.t) list -> t -> t

val subst_view_inv : (String.t * (Var.t list * Cpure.t)) list -> t -> (t * Cpure.t list)

val fv : t -> Var.t list

val star_decompose : t -> CpredNode.t list * CptoNode.t list

val sequentialize_views : t -> t

val subst_type : (typ * typ) list -> t -> t

val discard_ind_preds : t -> t

val contain_pred : t -> string -> bool

val subtract_pto : t -> CptoNode.t -> t

val subtract_pred : t -> CpredNode.t -> t

val update_view_unfold_number: int -> t -> t

val clear_view_unfold_step :  t -> t


val increase_view_unfold_number:  t -> t

val equal: t -> t -> bool
