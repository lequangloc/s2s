(*
This module checks sat for pure inductive predicate including
Horn clauses, Constrained Horn Clauses and Horn-like Clauses

*)

open Globals
open Gen.Basic
open VarGen


open Com

module CF = Cformula
module CSH = Csymheap
module CFU = CfUtil
module CPeN = CpredNode
module CP = Cpure

let check_sat_pure pdecls p=
  if is_sat_fnc p then Out.SAT, None
  else
    Out.UNSAT, None


(*
  all predicates in f is pure only
*)
let is_sat_chc pdecls f=
 Tpdispatcher.is_sat_chc pdecls f, None

let check_sat pdecls (f0 :CF.t) =
  if not !Globals.smt_horn then
    (* convert to pure using pred invs *)
    let invs = List.map (fun decl ->
        (decl.Cpred.pred_name, (decl.Cpred.pred_vars, decl.Cpred.pred_pure_inv))
    ) pdecls in
    let is_deci, defs = Dpi.to_pure_self_rec "NONE" [] false invs f0 in
    let _, _, p = List.hd defs in
    let r, cex = check_sat_pure pdecls p in
    if r == Out.UNSAT then r, cex
    else if r == Out.SAT && is_deci && CFU.is_pred_deci pdecls f0 then
      Out.SAT, cex
    else
      Out.UNKNOWN, None
  else
    is_sat_chc pdecls f0
