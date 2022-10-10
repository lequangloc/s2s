open Globals
open Gen.Basic
open VarGen

type rel_decl = {
    rel_name : ident;
    rel_typed_vars : Var.t list;
    rel_formula : Cpure.formula ; }

and t  = rel_decl

let string_of r = "rel decl"
