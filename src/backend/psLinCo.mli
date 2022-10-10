open Globals
open Gen
open VarGen

module CF = Cformula
module PeN = CpredNode
module PoN = CptoNode

module CP = Cpure

open EntRule

val ps_col: Cpred.t list -> bool -> EntNode.ENT_NODE_DATA.t -> (EntNode.ENT_NODE_DATA.t * t) list list * (Var.t * Var.t) list * Com.entstuck

val ps_pred_root_unfold: Cpred.t list -> EntNode.ENT_NODE_DATA.t ->
  (PeN.t list) -> (PeN.t list) ->  (Var.t * Var.t) list ->  (Var.t * Var.t) list ->  (Var.t * Var.t) list ->  (Var.t * Var.t) list ->  Var.t list ->  Var.t list ->  Var.t list -> Var.t -> bool * ((EntNode.ENT_NODE_DATA.t * t) list list * (Var.t * Var.t) list * Com.entstuck)


val do_left_unfold: Cpred.t list -> EntNode.ENT_NODE_DATA.t -> (Var.t * Var.t) list ->  (Var.t * Var.t) list ->  Var.t list ->  Var.t list ->  Var.t list -> (PeN.t * CF.t) list -> (EntNode.ENT_NODE_DATA.t * t) list list * (Var.t * Var.t) list * Com.entstuck

val do_right_unfold: Cpred.t list -> EntNode.ENT_NODE_DATA.t -> (Var.t * Var.t) list ->  (Var.t * Var.t) list ->  Var.t list ->  Var.t list ->  Var.t list -> (PeN.t * CF.t) list -> (EntNode.ENT_NODE_DATA.t * t) list list * (Var.t * Var.t) list * Com.entstuck

val do_base_linear_unfold: Cpred.t list -> EntNode.ENT_NODE_DATA.t -> bool -> (Var.t * Var.t) list ->  (Var.t * Var.t) list ->  Var.t list ->  Var.t list -> Var.t list -> (PeN.t * CF.t) list -> (EntNode.ENT_NODE_DATA.t * t) list
