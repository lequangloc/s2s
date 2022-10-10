open Globals
open Gen.Basic
open VarGen
open Gen

module CF = Cformula
module CP = Cpure
module PeN = CpredNode

module V = Var

type colem_decl =
{ (* IN *)
  (*DIFF starting acyc properties*)
  colem_root_args1: V.t list; colem_precise_args1: V.t list;
  colem_ext_largs1: V.t list;  colem_nl_ext_largs1: V.t list;
  colem_ext_rargs1: V.t list;  colem_nl_ext_rargs1: V.t list;
  colem_other_args1: V.t list; (* not compose vars *)

  colem_root_args2: V.t list;
  colem_precise_args2: V.t list; colem_ext_args2: V.t list;
  colem_nl_precise_args2: V.t list; colem_nl_ext_args2: V.t list;

  colem_root_args3: V.t list;
  colem_precise_args3: V.t list; colem_ext_args3: V.t list;
  colem_nl_precise_args3: V.t list; colem_nl_ext_args3: V.t list;

  colem_other_args3: V.t list; (* not compose vars *)
 (* OUT *)
  colem_qvars: V.t list;
  colem_frame: PeN.t;
  colem_rem: PeN.t list;
  colem_pure: CP.t;
  (* relational assumption list *)
}


type t = colem_decl


val string_of: t -> ident

val mk: V.t list -> V.t list -> V.t list -> V.t list -> V.t list -> V.t list ->
  V.t list ->
  V.t list ->  V.t list -> V.t list -> V.t list ->  V.t list ->
  V.t list ->  V.t list -> V.t list -> V.t list ->  V.t list ->
  V.t list ->
  V.t list -> PeN.t -> PeN.t list  -> CP.t -> t
