open Globals
open Gen.Basic
open VarGen

module PeN = CpredNode
module CF = Cformula
module CoRule = CcoRule

type pred_decl =
  {
    pred_name : ident;
    pred_vars : Var.t list;
    mutable pred_formula : Cformula.t;
    (* if the pred is complete and cycle (i.e., base case is htrue),
       do case split empty or at least one node for cycle *)
    mutable pred_pure_inv : Cpure.t; (*over-approximation*)
    mutable pred_base : CF.t list * CF.t list ;
    (* base-pair, complete when precise *)

    pred_unfolded_formula : Cformula.t list;
    (* with base pairs *)
    pred_formula_w_ctx : (Cpure.t * Cformula.t) list;
    (* for each branch, annotated with br_inv
       complete if br_inv1 /\ br_inv2 ==> false
           and     \top ==> (br_inv1 \/ br_inv2)
    *)

    pred_rec : rec_kind;
    mutable pred_is_sat_deci : bool;
    pred_is_ent_deci : bool;
    pred_is_shape_only : bool; (*shape only: based on type (consider based on disequality only)*)
    mutable pred_is_ent_base_reused : bool;
    pred_is_acyclic : bool; (*linear and acyclic*)
    pred_is_pure_acyclic : bool list; (* linear acyclic of pure properties *)
    pred_is_composable : bool; (*possible to apply composition rule*)
    mutable pred_compose_rule_same_ext_src: CoRule.t list;
    mutable pred_compose_rule_diff_ext_src: CoRule.t list;
    mutable pred_strengthen_rules: StreRule.t list;
    pred_is_pure : bool;


    (* precise preds *)
    (* pred_order: int; *)
    (*  source (null end) list *)
    pred_roots: Var.t list;
    pred_composition_vars: (((Var.t * Var.t) list * (Var.t * Var.t) list  * (Var.t * Var.t) list * (Var.t * Var.t) list * (Var.t * Var.t) list * Var.t list (* * (Var.t * Var.t) list *)) * ((Var.t * Var.t) list)) option;
        (* spatial (source * target) list *
         precise (decided by the root) local (source * target) list * extensible local (source * target) list *
        * precise non-local (source * target) list * extensible   non-local (source * target) list
        * boundary list
        * disjoint prs (e=f ==> base case) *)
    pred_bw_tars: Var.t list;

    pred_is_prim : bool;
    pred_data_name : ident;
    pred_parent_name: (ident) option;

    pred_pos : loc;
  }


type t = pred_decl

val string_of : t -> string

val get_pred_inv : t list -> Globals.ident -> Var.t list -> Cpure.t

val get_pred_all_inv : t list -> (Globals.ident * (Var.t list * Cpure.t)) list

val safe_unfold_num: t list -> string -> int

val get_root_src_tar_acyclic : t list -> string -> Var.t list -> Var.t list * Var.t list

val get_root_src_tar_composition : t list -> string -> Var.t list -> Var.t list * Var.t list

val get_all_src_tar_composition : t list -> string -> Var.t list -> Var.t list * Var.t list * Var.t list * Var.t list * Var.t list * Var.t list * Var.t list * Var.t list * Var.t list * Var.t list * Var.t list

(*both cyclic and acyclic*)
val get_root_src_composition : t list -> string -> Var.t list -> Var.t list

val get_root_tar_composition : t list -> string -> Var.t list -> bool * Var.t list

val extract_roots: t list -> CpredNode.t -> Var.t list

val is_pred_acyclic: t list -> ident -> bool

val search_pred_base_linear_unfold: t list ->
  PeN.t list -> (Var.t * Var.t) list -> Var.t list -> (PeN.t * CF.t) list

val search_unfold_emp_branch: t list -> PeN.t list -> bool * (PeN.t * CF.t) list list


val get_composition_rule: t list -> ident ->
  Var.t list -> Var.t list -> Var.t list -> Var.t list -> Var.t list -> Var.t list->
  Var.t list->
  Var.t list -> Var.t list -> Var.t list -> Var.t list -> Var.t list ->
  Var.t list -> Var.t list -> Var.t list -> Var.t list -> Var.t list ->
  Var.t list -> (Var.t list * PeN.t list * Cpure.t) list

val get_strengthen_rules: t list -> ident -> Var.t list -> PeN.t list

val is_progressing: t -> bool
