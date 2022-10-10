open Globals
open Gen.Basic
open VarGen

module PeN = CpredNode
module CF = Cformula
module CoRule = CcoRule

val generate_composable_rule: Cpred.t list -> ident -> Var.t list -> Cpure.t -> bool ->
 (Var.t * Var.t) list -> (Var.t * Var.t) list -> (Var.t * Var.t) list -> (Var.t * Var.t) list -> (Var.t * Var.t) list
  -> CoRule.t list * CoRule.t list

val generate_strengthen_rules: Cpred.t list -> Cpred.t -> StreRule.t list
