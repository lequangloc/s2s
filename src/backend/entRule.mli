open Globals
open Gen
open VarGen


module CF = Cformula
module PeN = CpredNode
module PoN = CptoNode

module CP = Cpure

module SLND = SlNode.SL_NODE_DATA
module SLN = SlNode
module EQ = Eql

module ENT = EntNode.ENT_NODE_DATA
module E = EntNode

type frame_pto = {
    lhs_node : PoN.t; (* left points-to*)
    rhs_node: PoN.t; (* right points-to*)
    lhs_subst: Var.pair list; (* possibly empty -> no subst *)
    rhs_subst: Var.pair list; (* possibly empty -> no subst *)
    rhs_proven: CP.t option; (* added to RHS for proving *)
}


type frame_pred = {
    lhs_node : PeN.t; (* left points-to*)
    rhs_node: PeN.t; (* right points-to*)
    lhs_subst: Var.pair list; (* possibly empty -> no subst *)
    rhs_subst: Var.pair list; (* possibly empty -> no subst *)
    rhs_proven: CP.t option; (* added to RHS for proving *)
}

type ent_inf =
  | IR_FR_PTO of frame_pto
  | IR_FR_PRED of frame_pred
        (* left predicate occurence * right predicate occurence *)
  | IR_LUNFOLD of (PeN.t * CF.t)
  | IR_LB_BASE_UNFOLD of (PeN.t list * CF.t)
  | IR_TW_BASE_UNFOLD of (ENT.t)
        (* left predicate occurence * branch formula *)
  | IR_RUNFOLD of (PeN.t * CF.t)
        (* right predicate occurence * branch formula *)
  | IR_RCOMPOSE of (PeN.t * PeN.t * PeN.t list)
  | IR_LCOMPOSE of (PeN.t * PeN.t * PeN.t list)
  | IR_RSTRE of (PeN.t * PeN.t * PeN.t)
      (* right predicate occurence * frame pred * residual pred*)
  | IR_CC of (int * int * (Var.t * Var.t) list)
        (* companion id * bud id * subtitution *)
  | IR_SUBST of (Var.t * Var.t) list
  | IR_RINST of (Var.t * Var.t) list
  | IR_RNON_INST of PeN.t list
  | IR_AXIOM_OVER of CF.t
        (*over - approximate LHS -> false. including not(E=E) *)
  | IR_EX_MIDD of (Var.t * Var.t * bool) (*E=F \/ E!=F*)
  | IR_HYPO of (SLND.t * SLND.t)
  | IR_LBase of PeN.t
  | IR_RBase of PeN.t
  | IR_EX_LHS of (Var.t * Var.t) list
  | IR_EX_EQ_RHS of (Var.t * Var.t) list
  | IR_SEQ of (ent_inf * ent_inf)

type t = ent_inf


val string_of : t -> string

val subst : (Var.t * Var.t) list -> t -> t

val flatten_proofs : t -> t list

val is_frame_pred_wo_cond : t -> bool

val is_match_pred : Cpred.t list -> EntNode.ENT_NODE_DATA.t -> bool

val construct_ccut : Cpred.t list -> int -> int -> (Var.t * Var.t) list -> EntNode.ENT_NODE_DATA.t -> (PeN.t list * PoN.t list * Cpure.t * SlNode.SL_NODE_DATA.t) -> (EntNode.ENT_NODE_DATA.t * t) list

(*match pto*)
val find_pto_match: PoN.pto list ->  PoN.pto list ->
  (Var.t * Var.t) list -> (Var.t * Var.t) list -> (PoN.pto * PoN.pto) list

val ps_rhs_instantiate:  Cpred.t list ->  ENT.t -> (Var.t * Var.t) list -> (ENT.t * ent_inf) list

val proof_search_match_point_to: Cpred.t list ->  ENT.t ->   PoN.pto * PoN.pto ->  Var.t list ->  SLND.t ->
  Var.t list -> SLND.t -> (ENT.t * ent_inf) list * (Var.t * Var.t) list

(*match pred*)
val find_pred_match: Cpred.t list -> PeN.t list -> Var.t list ->
  (Var.t * Var.t) list -> Var.t list -> PeN.t list ->
  Var.t list -> (Var.t * Var.t) list -> Var.t list -> (PeN.t * PeN.t) list * (PeN.t * PeN.t) list * (PeN.t * PeN.t) list

val find_diff_pred_match: Cpred.t list -> PeN.t list -> Var.t list ->
  (Var.t * Var.t) list -> Var.t list -> PeN.t list ->
  Var.t list -> (Var.t * Var.t) list -> Var.t list -> (PeN.t * PeN.t) list * (PeN.t * PeN.t) list * (PeN.t * PeN.t) list

val proof_search_match_pred_cond: Cpred.t list -> ENT.t ->
  PeN.hpred * PeN.hpred -> (Var.t * Var.t) list ->
  (Var.t * Var.t) list -> (EntNode.ENT_NODE_DATA.t * ent_inf) list

(*unfold*)
val unfold_pred: Cpred.t list -> PeN.t -> (PeN.t * CF.t) list

val proof_search_composition_right_unfold: Cpred.t list ->  ENT.t -> (PeN.t * PeN.t) -> (ENT.t * ent_inf) list

val proof_search_composition_left_unfold: Cpred.t list ->  ENT.t -> (PeN.t * PeN.t) -> (ENT.t * ent_inf) list

val proof_search_strengthen_unfold: Cpred.t list ->  ENT.t -> (PeN.t * PeN.t) -> (ENT.t * ent_inf) list

(*RInd*)
val search_pred_with_match_alloca:  Cpred.t list -> bool ->
 PeN.t list -> (Var.t * Var.t) list -> Var.t list -> (PeN.t * CF.t) list * (Var.t * Var.t) list

val proof_search_unfold: ?ctx_pruning:bool -> Cpred.t list ->
  ENT.t -> bool -> (EQ.V.t * EQ.V.t) list -> (Var.t * Var.t) list -> Var.t list -> Var.t list -> Var.t list -> (PeN.hpred * CF.t) list -> (ENT.t * ent_inf) list

val proof_search_left_base_unfold: ?ctx_pruning:bool -> Cpred.t list ->
  ENT.t -> (EQ.V.t * EQ.V.t) list -> (Var.t * Var.t) list -> Var.t list -> Var.t list -> Var.t list -> (PeN.hpred list * CF.t) list -> (ENT.t * ent_inf) list

val proof_search_unfold_seq: ?ctx_pruning:bool -> Cpred.t list ->
  ENT.t -> bool -> (EQ.V.t * EQ.V.t) list -> (Var.t * Var.t) list -> Var.t list -> Var.t list -> Var.t list -> ((PeN.hpred * CF.t) list) list -> (ENT.t * ent_inf) list

val proof_search_unfold_dupl_roots: ?ctx_pruning:bool -> Cpred.t list ->
  ENT.t -> bool -> (EQ.V.t * EQ.V.t) list -> (Var.t * Var.t) list -> Var.t list -> Var.t list -> Var.t list -> PeN.hpred list -> Var.t list ->  PeN.hpred list -> (ENT.t * ent_inf) list

(*EX-MID*)
val check_excluded: Var.t list -> Var.t list -> (Var.t * Var.t) list -> (Var.t * Var.t) option

val ps_exclude_middle: Cpred.t list -> (Var.t * Var.t) -> bool
 -> PeN.hpred -> ENT.t -> (E.ENT_NODE_DATA.t * ent_inf) list

(*LBase*)
val search_pred_base_case: Cpred.t list -> CpredNode.t -> (CpredNode.t * CF.t) list

(*P <-> Q. LInd*)
val find_pred_root_match: Cpred.t list -> bool -> PeN.t list ->
  (Var.t * Var.t) list ->
  PeN.t list -> (Var.t * Var.t) list -> (PeN.t * PeN.t) list

val proof_search_left_unfold_pred: Cpred.t list ->
  ENT.t -> CpredNode.t -> (Var.t * Var.t) list -> (Var.t * Var.t) list -> (Var.t * Var.t) list  ->  Var.t list -> Var.t list -> Var.t list -> ((ENT.t * ent_inf) list list * (Var.t * Var.t) list * Com.entstuck)



