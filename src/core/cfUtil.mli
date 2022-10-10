open Globals
open Gen
open VarGen

module CF = Cformula
module CPred = Cpred
module CP = Cpure

val unfold: ?bfs:bool -> CF.t -> CF.t list

val unfold_base_pair : CPred.t list -> bool -> CF.t -> CF.t list

val is_pure : CPred.t list -> string list -> CF.t -> bool

val is_pred_deci : Cpred.t list -> CF.t -> bool

val get_closure_preds : Cpred.t list -> CF.t list ->  Cpred.t list ->  Cpred.t list

val check_pred_precise: Cpred.t list -> string -> Var.t list -> CF.t -> Var.t list * ( (((Var.t * Var.t) list * (Var.t * Var.t) list * (Var.t * Var.t) list * (Var.t * Var.t) list * (Var.t * Var.t) list  * Var.t list) * (Var.t * Var.t) list) option) * Var.t list * bool * bool * bool list

val extend_pred_defn: string -> Var.t list  ->  Var.t list  -> ((((Var.t * Var.t) list *(Var.t * Var.t) list * (Var.t * Var.t) list * (Var.t * Var.t) list * (Var.t * Var.t) list * Var.t list) * (Var.t * Var.t) list) option) -> CF.t -> CF.t list

val unfold_pred : Cpred.t list -> CpredNode.t -> CF.t

val compute_br_inv: Cpred.t list -> string -> Var.t list -> CF.t -> Var.t list -> ((((Var.t * Var.t) list  * (Var.t * Var.t) list * (Var.t * Var.t) list * (Var.t * Var.t) list  * (Var.t * Var.t) list * Var.t list) * (Var.t * Var.t) list) option) -> (Cpure.t * CF.t) list
(*
  brach_inv is used for context-sensitive unfolding
  TODO: extend for the fragment outside of the linear fragment
*)

val sequentialize_and_unfold_flat_views: Cpred.t list -> CF.t -> CF.t
(*
 - unfold non-rec view
 - ordering the remaining views
*)

val set_progressing_step: CF.t -> CF.t

(*ex u. x = u+k*)
val skolem_rhs_arith: Var.t list ->  CF.t -> (CF.t * CP.t) option
