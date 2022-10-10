open Globals
open Gen
open VarGen

open Com

module CF = Cformula
module CSH = Csymheap
module CH = Cheap
module CPeN = CpredNode
module CPoN = CptoNode
module CP = Cpure
module EQ =Eql

let inv_pred_to_abs_pure pdecls (preds : CPeN.t list) =
  let invs = List.map (fun p ->
      let pdecl = List.find (fun decl ->
          Ustr.str_eq p.CPeN.hpred_name decl.Cpred.pred_name) pdecls in
      let sst = List.combine pdecl.Cpred.pred_vars p.CPeN.hpred_arguments in
      CP.subst_var sst (CP.fresh_quantifiers pdecl.Cpred.pred_pure_inv)
  ) preds in
  let inv, eqNulls, neqNulls, eqs, diseqs = List.fold_left
    (fun (ap, aeqNulls, aneqNulls, aeqs, adiseqs) p1->
        let np = Cpure.mkAnd ap p1 no_pos in
        let eqNulls, neqNulls, eqs, diseqs, _ = Cpure.type_decomp p1 in
        np, aeqNulls@eqNulls, aneqNulls@neqNulls, aeqs@eqs, adiseqs@diseqs
    ) (Cpure.mkTrue no_pos, [],  [], [], []) invs in
  (inv, (eqNulls, neqNulls, eqs, diseqs))


let star_decompose pdecls f=
  let star_decompose_sbh qvars fb=
    let preds, ptos = CH.star_decompose fb.CSH.base_heap in
    let eqnull, neqnull, eqs, diseqs, arith = CP.type_decomp fb.CSH.base_pure in
    let pto_neqnull, pto_neqs = CPoN.to_abs_pure ptos in
    let () = Debug.ninfo_hprint (add_str  "pto_neqs" (pr_list (pr_pair Var.string_of Var.string_of))) pto_neqs no_pos in
    let neqnull = (neqnull@pto_neqnull) in
    let diseqs = (diseqs@pto_neqs) in
    (* qf and existentially quantified *)
    let eql_f, qf_eql_f = if qvars != [] then
      let qf_eqnull = List.filter (fun sv -> not (Var.mem sv qvars)) eqnull in
      let qf_neqnull = List.filter (fun sv -> not (Var.mem sv qvars)) neqnull in
      let qf_eqs = List.filter (fun (sv1, sv2) -> Var.intersect [sv1;sv2] qvars == []) eqs in
      let qf_diseqs = List.filter (fun (sv1, sv2) -> Var.intersect [sv1;sv2] qvars == []) diseqs in
      let () = Debug.ninfo_hprint (add_str  "qf_diseqs" (pr_list (pr_pair Var.string_of Var.string_of))) qf_diseqs no_pos in
      EQ.mk qvars eqnull neqnull eqs diseqs, EQ.mk [] qf_eqnull qf_neqnull qf_eqs qf_diseqs
    else
      let eql = EQ.mk qvars eqnull neqnull eqs diseqs in
      eql, eql
    in
    let inv_preds, (inv_eqNulls, inv_neqNulls, inv_eqs, inv_diseqs) = inv_pred_to_abs_pure pdecls preds in
    let ho_inv_preds = EQ.mk qvars inv_eqNulls inv_neqNulls inv_eqs inv_diseqs in
    (qvars, pto_neqnull, preds, ptos, qf_eql_f, eql_f, arith, inv_preds, ho_inv_preds)
  in
  match f with
    | CF.Base fb -> star_decompose_sbh [] fb
    | CF.Exists (fb, qvars) -> star_decompose_sbh (Var.remove_dups qvars) fb
    | CF.Or _ -> Gen.report_error no_pos "sl_util: not support or"

let is_relative_complete qvars rest_bud_views matched_bud_views=
  let rec is_pair_wise_diff used_svs bud_views=
    match bud_views with
      | vn::rest ->
            let args1 = vn.CPeN.hpred_arguments in
            if Var.intersect args1 used_svs != [] ||
              List.exists (fun vn1 -> Var.intersect args1 vn1.CPeN.hpred_arguments
                  != []
              ) rest
            then
              false
            else is_pair_wise_diff used_svs rest
      | [] -> true
  in
  if rest_bud_views == [] then
    (* complete cycle *)
    true
  else
    (* still have univ parameters *)
    (* if List.exists (fun vn -> *)
    (*     Var.diff vn.CPeN.hpred_arguments qvars != [] *)
    (* ) rest_bud_views then *)
    (*   false *)
    (* else *)
    let used_svs = List.fold_left (fun r vn ->
        r@vn.CPeN.hpred_arguments
    ) [] matched_bud_views in
    is_pair_wise_diff used_svs rest_bud_views
