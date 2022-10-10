open Globals
open Gen
open VarGen

open Exp
open Var

(*
label for an edge in S2SL
*)
module STR_EDGE_LBL = struct
  type t = (Var.t * Exp.t) list

  let empty : t = []

  let is_empty (l:t) : bool = l==[]

  let string_of (l: t) : string = (pr_list (pr_pair Var.string_of Exp.string_of) ) l
  let subst (sst : (Var.t * Var.t) list) (l : t) : t=
      List.map (fun ((sv1, t1)) ->
          let sv11 = Var.subst sst sv1 in
          let t11 = Exp.subst sst t1 in
          (sv11, t11)
      )l
end;;

module STREDGE = Edge.FEdge(STR_EDGE_LBL)
