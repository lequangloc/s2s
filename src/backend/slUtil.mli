open Globals
open Gen
open VarGen

open Com

module CF = Cformula
module CSH = Csymheap
module CH = Cheap
module CPeN = CpredNode
module CPoN = CptoNode
module CP = Cpure


val star_decompose :  Cpred.t list -> CF.t -> Var.t list * Var.t list * CPeN.t list *
  CPoN.t list * Eql.t * Eql.t * CP.t * CP.t * Eql.t

(* val ent_eval_base_2sides : Cpred.t list -> CF.t -> CF.t -> Cheap.t -> Out.t *)
val is_relative_complete : Var.t list -> CPeN.t list -> CPeN.t list -> bool
