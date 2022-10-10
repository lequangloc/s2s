open Globals
open Gen.Basic
open VarGen
open Gen

module IF = Iformula
module IP = Ipure

type pred_decl =
  {
    pred_name : ident;
    mutable pred_vars : ident list;
    pred_formula : IF.t;
    pred_pos : loc;
    pred_is_prim : bool;
    (* pred_kind : pred_kind; *)

    mutable pred_data_name : ident;

    mutable pred_typed_vars : (typ * ident) list;
    pred_parent_name: (ident) option;
    pred_invariant : IP.formula; }

type t = pred_decl


let string_of v = "\npred " ^ v.pred_name ^ "< " ^
  (String.concat "," v.pred_vars) ^ "> == " ^
  (IF.string_of v.pred_formula) ^
  "\n inv " ^ (IP.string_of v.pred_invariant) ^ "."
