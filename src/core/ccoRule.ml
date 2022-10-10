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
  colem_ext_largs1: V.t list; colem_nl_ext_largs1: V.t list;
  colem_ext_rargs1: V.t list; colem_nl_ext_rargs1: V.t list;
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

let string_of e=
  "root_args1"^ ( V.string_of_list e.colem_root_args1)^"; precise_args1:"^ ( V.string_of_list e.colem_precise_args1)^
      "\n (LHS) ext_largs1:"^ ( V.string_of_list e.colem_ext_largs1)^"; ext_nl_ext_largs1:"^ ( V.string_of_list e.colem_nl_ext_largs1)^ "\n (RHS) ext_rargs1:"^ ( V.string_of_list e.colem_ext_rargs1)^"; nl_ext_rargs1:"^ ( V.string_of_list e.colem_nl_ext_rargs1)^
      "; colem_other_args1:"^ ( V.string_of_list e.colem_other_args1)^

    "\n" ^ "(LHS tars) root_args2:"^ ( V.string_of_list e.colem_root_args2)^ "; precise_args2:"^ ( V.string_of_list e.colem_precise_args2)^
      "; ext_args2:"^ ( V.string_of_list e.colem_ext_args2)^
      "; nl_precise_args2:"^ ( V.string_of_list e.colem_nl_precise_args2)^
      "; nl_ext_args2:"^ ( V.string_of_list e.colem_nl_ext_args2)^

  "\n" ^ "(RHS tars) root_args3:"^ ( V.string_of_list e.colem_root_args3)^ "; precise_args3:"^ ( V.string_of_list e.colem_precise_args3)^
       "; ext_args3:"^ ( V.string_of_list e.colem_ext_args3)^
       "; nl_precise_args3:"^ ( V.string_of_list e.colem_nl_precise_args3)^
      "; nl_ext_args3:"^ ( V.string_of_list e.colem_nl_ext_args3)^
      "; colem_other_args3:"^ (V.string_of_list e.colem_other_args3)^

      "\n <==" ^ " Ex " ^ (V.string_of_list e.colem_qvars)^". "
  ^(PeN.string_of e.colem_frame) ^" * "^ (String.concat "*" (List.map PeN.string_of e.colem_rem)) ^" && "^(CP.string_of e.colem_pure)

let mk root_args1 precise_args1 ext_largs1 nl_ext_largs1
      ext_rargs1 nl_ext_rargs1 other_args1
      root_args2 precise_args2 ext_args2 nl_precise_args2 nl_ext_args2
      root_args3 precise_args3 ext_args3 nl_precise_args3 nl_ext_args3
      other_args3
      qvars frame_vn vns p
      =
  {
      (* for diff only *)
      colem_root_args1 = root_args1; colem_precise_args1 = precise_args1;
      colem_ext_largs1=ext_largs1;  colem_nl_ext_largs1=nl_ext_largs1;
      colem_ext_rargs1 = ext_rargs1; colem_nl_ext_rargs1=nl_ext_rargs1;
      (*end for diff*)
      colem_other_args1 = other_args1;

      colem_root_args2=root_args2;
      colem_precise_args2=precise_args2; colem_ext_args2=ext_args2;
      colem_nl_precise_args2=nl_precise_args2; colem_nl_ext_args2=nl_ext_args2;

      colem_root_args3=root_args3;
      colem_precise_args3=precise_args3; colem_ext_args3=ext_args3;
      colem_nl_precise_args3=nl_precise_args3; colem_nl_ext_args3=nl_ext_args3;

      colem_other_args3 = other_args3;

      colem_qvars = qvars;
      colem_frame = frame_vn;
      colem_rem = vns;
      colem_pure = p;
  }
