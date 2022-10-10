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


let mk co_args cut_args other_args rem_seg p=
  {
      colem_co_args = co_args;
      colem_cut_args = cut_args;
      colem_other_args = other_args;
      colem_rem = rem_seg;
      colem_pure = p;
  }
