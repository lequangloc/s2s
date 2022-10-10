open Globals
open Gen
open VarGen


module CF = Cformula
module PN = CpredNode

module ER = EntRule

(*
label for an edge in S2SL
*)
module ENT_EDGE_LBL = struct
  type t = ER.t list

  let empty : t = []

  let is_empty (l:t) : bool = l==[]

  let string_of e : string = (pr_list ER.string_of) e
  let subst (sst : (Var.t * Var.t) list) (l : t) : t=
    List.map (ER.subst sst) l
end;;

module ENTEDGE = Edge.FEdge(ENT_EDGE_LBL)
