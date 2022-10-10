(*
data structure declaration
*)

open Globals
open Gen.Basic
open Gen
open VarGen

type data_decl = {
    data_name : ident;
    mutable data_fields : (typed_ident * (ident list)) list;
    data_fields_new : (Var.t * (ident list)) list;
    data_parent_name : ident;
    data_pos : loc;
    }

type t = data_decl

let rec string_of d=
  "\ndata " ^ d.data_name ^ " {\n" ^ (string_of_fields d.data_fields "\n") ^ "\n}."

and string_of_field (d, ann) = match d with
  | (t, i)             -> (* (if il then "inline " else "") ^ *)
        (string_of_typ t) ^ " " ^ i ^ ("@"^(String.concat "@" ann)) ^ ";"

and string_of_fields l c = match l with
  | []               -> ""
  | h::[]            -> "  " ^ string_of_field h
  | h::t             -> "  " ^ (string_of_field h)
        ^ ";" ^ c ^ (string_of_fields t c)
