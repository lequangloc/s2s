open Globals
open Ustr
open VarGen
open Gen.Basic

val compute_inv_scc : String.t list -> Cpred.pred_decl list -> Cpred.pred_decl list

val compute_inv : Globals.ident -> Var.t list ->  Cformula.t -> bool -> rec_kind -> bool -> Cpred.t list -> Cpure.t -> bool * Cpure.t

val compute_fixpt : String.t list ->  String.t ->   Var.t list -> Cformula.t -> bool -> rec_kind -> bool -> Cpred.t list -> Cpure.t -> bool * Cpure.t
