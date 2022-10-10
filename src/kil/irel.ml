open Globals
open Gen.Basic
open VarGen

type rel_decl = {
    rel_name : ident;
    rel_typed_vars : (typ * ident) list;
    rel_formula : Ipure.formula ; }

and t  = rel_decl

let string_of r = "rel decl"
