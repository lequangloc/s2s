open Globals
open Gen
open VarGen

module CF = Cformula
module PeN = CpredNode
module PoN = CptoNode

module CH = Cheap

module CP = Cpure

module SUBT = EntType.SUBT

val search_match_comp_view:  Cpred.t list -> SUBT.t list -> PeN.t -> Var.t list -> PeN.t list -> Var.t list -> PeN.t

val search_match_comp_views:  Cpred.t list -> SUBT.t list -> PeN.t list -> Var.t list -> PeN.t list -> Var.t list -> (PeN.t * PeN.t) list * bool * (Var.t * Var.t) list

val search_match_bud_pto: bool -> (Var.t * Var.t) list -> PoN.t list -> Var.t list -> (Var.t * Var.t) list -> PoN.t list -> Var.t list -> (Var.t * Var.t) list -> PoN.t list * (Var.t * Var.t) list * PoN.t list

val is_match_rhs_back_link : (Var.t * Var.t) list -> SlNode.SL_NODE_DATA.t -> SlNode.SL_NODE_DATA.t -> PoN.t list -> CH.t -> bool

(*unify numeric of views with the same spatial args
 in cons of bud and comp *)
val unify_views_same_spatial: (Var.t * Var.t) list -> SlNode.SL_NODE_DATA.t -> SlNode.SL_NODE_DATA.t -> (Var.t * Var.t) list
