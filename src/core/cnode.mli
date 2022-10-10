open Globals
open Gen.Basic
open VarGen


type data_decl = { 
    data_name : ident;
    mutable data_fields : (typed_ident * (ident list)) list;
    data_fields_new : (Var.t * (ident list)) list;
    data_parent_name : ident;
    data_pos : loc;
}

type t = data_decl


val string_of: t -> string

