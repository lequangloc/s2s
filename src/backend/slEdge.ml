open Globals
open Gen
open VarGen


module CF = Cformula
module PN = CpredNode

(*
label for an edge in S2SL
*)
module SL_EDGE_LBL = struct
  type t = (PN.t * CF.t) list

  let empty : t = []

  let is_empty (l:t) : bool = l==[]

  let string_of (l: t) : string = (pr_list (pr_pair PN.string_of CF.string_of) ) l
  let subst (sst : (Var.t * Var.t) list) (l : t) : t=
    List.map (fun ((p1, f1)) ->
        let p11 = PN.subst sst p1 in
        let f11 = CF.subst sst f1 in
        (p11, f11)
    ) l
end;;

module SLEDGE = Edge.FEdge(SL_EDGE_LBL)
