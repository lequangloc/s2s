open Globals
open Gen.Basic
open VarGen

module CPN = CpredNode
module CPtoN = CptoNode

type formula =
  | Star of (formula * formula * loc)
  | PtoNode of CptoNode.pto
  | PredNode of CpredNode.hpred
  | HEmp
  | HTrue
  | HFalse

and t = formula

let string_of h0=
  let rec helper h= match h with
    | Star (h1, h2, _) -> (helper h1) ^ " * " ^ (helper h2)
    | PtoNode n -> CptoNode.string_of n
    | PredNode n -> CpredNode.string_of n
    | HEmp -> "emp"
    | HTrue -> "htrue"
    | HFalse -> "hfalse"
  in
  helper h0

let mkHTrue p = HTrue

let mkHFalse p = HFalse

let mkPtoNode pto_sv pred_args data_name dr holes l=
  PtoNode (CptoNode.mkPtoNode pto_sv data_name dr pred_args holes l)

let mkPredNode pred_name dr pred_args l=
  PredNode (CpredNode.mk pred_name dr pred_args l)

let mkStarAnd h1 h2 l=
  match h1, h2 with
    | HEmp, HEmp -> HEmp
    | HEmp, _ -> h2
    | _ , HEmp -> h1
    | HFalse, _ -> HFalse
    | _ , HFalse -> HFalse
    | HTrue, HTrue -> HTrue
    | _ ->  Star (h1, h2, l)


let rec h_subst sst h= match h with
  | Star (h1, h2, pos) -> Star (h_subst sst h1, h_subst sst h2, pos)
  | PredNode p -> PredNode (CPN.subst sst p)
  | PtoNode pto -> PtoNode (CPtoN.subst sst pto)
  | HTrue -> h
  | HFalse -> h
  | HEmp -> h

let rec subst_type t_sst h= match h with
  | Star (h1, h2, pos) -> Star (subst_type t_sst h1, subst_type t_sst h2, pos)
  | PredNode p -> PredNode (CPN.subst_type t_sst p)
  | PtoNode pto -> PtoNode (CPtoN.subst_type t_sst pto)
  | HTrue -> h
  | HFalse -> h
  | HEmp -> h

let subst_view_inv pred_invs (hf0: t)=
  let rec helper hf= match hf with
    | Star (h1, h2, pos) -> begin
        let nh1, ps1 = helper h1 in
        let nh2, ps2 = helper h2 in
        match nh1,nh2 with
          | HEmp,HEmp -> HEmp,ps1@ps2
          | HEmp,_ -> nh2,ps1@ps2
          | _ , HEmp -> nh1,ps1@ps2
          | _ -> (Star (nh1, nh2, pos), ps1@ps2)
      end
    | PredNode vn -> begin
        try
          let (_,(form_args, inv)) = List.find (fun (s1,_) ->
              String.compare s1 vn.CPN.hpred_name = 0) pred_invs in
          let sst = List.combine form_args (vn.CPN.hpred_arguments) in
          (HEmp, [ (Cpure.subst_var sst inv)])
        with _ -> hf,[]
      end
    | _ -> hf,[]
  in helper hf0

let fv (h0 : t) : Var.t list =
  let rec aux h = match h with
    | Star (h1, h2, _) ->  Var.remove_dups (aux h1 @ aux h2)
    | PtoNode ({CPtoN.hpto_node = v;
      CPtoN.hpto_arguments = vs}) ->  Var.remove_dups ([v]@vs)
    | PredNode ({CPN.hpred_arguments = vs}) ->
          Var.remove_dups vs
    | HTrue | HFalse | HEmp -> []
  in aux h0


let star_decompose h0=
  let rec helper h= match h with
    | Star (h1, h2, _) ->
          let preds1, ptos1 = helper h1 in
          let preds2, ptos2 = helper h2 in
          (preds1@preds2, ptos1@ptos2)
    | PtoNode pto -> ([], [pto])
    | PredNode pred -> ([pred], [])
    | _ -> ([],[])
  in
  helper h0

let sequentialize_views h0=
  let rec helper sn h= match h with
    | Star (h1, h2, pos) ->
          let new_h1, sn1 = helper sn h1 in
          let new_h2, sn2 = helper sn1 h2 in
           (Star (new_h1, new_h2, pos), sn2)
    | PredNode pred -> (PredNode {pred with CPN.hpred_unfold_seq = sn}, (sn+1))
    | _ -> (h, sn)
  in
  let new_h, _ = helper 0 h0 in
  new_h

let discard_ind_preds h0=
  let rec aux h= match h with
    | Star (h1, h2, pos) -> begin
        let nh1 = aux h1 in
        let nh2 = aux h2 in
        match nh1, nh2 with
          | HEmp, _ -> nh2
          | _, HEmp -> nh1
          | _ -> Star (nh1, nh2, pos)
      end
    | PredNode _ -> HEmp
    | _ -> h
  in aux h0

let contain_pred h0 pred_name=
  let rec aux h= match h with
    | Star (h1, h2, _) -> (aux h1) || (aux h2)
    | PredNode pred -> Ustr.str_eq pred.CPN.hpred_name pred_name
    | _ -> false
  in aux h0

(* remove all matched ptos *)
let subtract_pto h0 pto=
  let rec aux h= match h with
    | PtoNode n ->
          if CptoNode.equal n pto then HEmp else PtoNode n
    | Star (h1, h2, pos) -> begin
          let nh1 = aux h1 in
          let nh2 = aux h2 in
          match nh1, nh2 with
            | HEmp, _ -> nh2
            | _, HEmp -> nh1
            | _ -> Star (nh1, nh2, pos)
      end
    | _ -> h
  in aux h0

(* remove all matched preds *)
let subtract_pred h0 vn=
  let rec aux h= match h with
    | PredNode n ->
          if CpredNode.equal n vn then HEmp else PredNode n
    | Star (h1, h2, pos) -> begin
          let nh1 = aux h1 in
          let nh2 = aux h2 in
          match nh1, nh2 with
            | HEmp, _ -> nh2
            | _, HEmp -> nh1
            | _ -> Star (nh1, nh2, pos)
      end
    | _ -> h
  in aux h0

let update_view_unfold_number num h0=
  let rec aux h= match h with
    | PredNode n ->
          PredNode {n with CPN.hpred_unfold_num = num}
    | Star (h1, h2, pos) -> begin
        Star (aux h1, aux h2, pos)
      end
    | _ -> h
  in aux h0

let clear_view_unfold_step h0=
  let rec aux h= match h with
    | PredNode n ->
          PredNode {n with CPN.hpred_unfold_step = 0}
    | Star (h1, h2, pos) -> begin
        Star (aux h1, aux h2, pos)
      end
    | _ -> h
  in aux h0

let increase_view_unfold_number h0=
  let rec aux h= match h with
    | PredNode n ->
          PredNode {n with CPN.hpred_unfold_num = n.CPN.hpred_unfold_num + 1}
    | Star (h1, h2, pos) -> begin
        Star (aux h1, aux h2, pos)
      end
    | _ -> h
  in aux h0

let equal h1 h2 = match h1, h2 with
  | HEmp, HEmp
  | HTrue, HTrue
  | HFalse, HFalse -> true
  | _ -> begin
        let cpreds1, cptos1 = star_decompose h1 in
        let cpreds2, cptos2 = star_decompose h2 in
        (List.for_all (fun cpred2 ->
            List.exists (fun cpred1 -> CPN.equal cpred1 cpred2) cpreds1
        ) cpreds2 ) &&
            ( List.for_all (fun cpred2 ->
                List.exists (fun cpred1 -> CPtoN.equal cpred1 cpred2 ) cptos1
            ) cptos2 )
    end
