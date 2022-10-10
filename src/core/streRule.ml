open Globals
open Gen.Basic
open VarGen
open Gen

module CF = Cformula
module CP = Cpure
module PeN = CpredNode

module V = Var

type strelem_decl =
{ (* IN *)
  strelem_args: V.t list;
    (* OUT *)
  strelem_heap: PeN.t;
}

type t = strelem_decl

let string_of e=
  "args" ^ ( V.string_of_list e.strelem_args) ^ ": " ^ (PeN.string_of e.strelem_heap)  ^ " <== "

let mk svs h= {
    strelem_args = svs;
    strelem_heap = h;
}
