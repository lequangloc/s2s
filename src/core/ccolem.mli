open Globals
open Gen.Basic
open VarGen
open Gen

module CF = Cformula
module CP = Cpure
module PeN = CpredNode

module V = Var

type corule_decl =
{
  colem_co_args: (V.t * V.t) list;
  colem_cut_args: V.t list; (* |colem_cut_args| = | colem_co_args | *)
  colem_other_args: V.t list; (* not compose vars *)
  colem_rem: PeN.t;
  colem_pure: CP.t;
  (* relational assumption list *)
}


type t = corule_decl

val mk: (V.t * V.t) list -> V.t list -> V.t list -> PeN.t
  -> CP.t -> t
