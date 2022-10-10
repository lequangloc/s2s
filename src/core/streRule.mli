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

val string_of: t -> ident

val mk: V.t list ->  PeN.t -> t
