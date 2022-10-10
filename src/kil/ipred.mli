open Globals
open Gen.Basic
open VarGen

type pred_decl =
  {
    pred_name : ident;
    mutable pred_vars : ident list;
    pred_formula : Iformula.t;
    pred_pos : loc;
    pred_is_prim : bool;
    (* pred_kind : pred_kind; *)

    mutable pred_data_name : ident;

    mutable pred_typed_vars : (typ * ident) list;
    pred_parent_name: (ident) option;
    pred_invariant : Ipure.formula; }

type t = pred_decl

val string_of : t -> string
