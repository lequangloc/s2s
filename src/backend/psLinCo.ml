(*
proof search for compositionally linear predicates
*)

open Globals
open Gen
open VarGen

module CF = Cformula
module PeN = CpredNode
module PoN = CptoNode

module CH = Cheap

module CP = Cpure

module SLND = SlNode.SL_NODE_DATA
module SLN = SlNode
module EQ = Eql

module ENT = EntNode.ENT_NODE_DATA
module E = EntNode

open Com
open EntRule

(* let ps_ctx_unfold cpreds e lvns rvns leqNulls reqNulls leqs reqs lneqs rneqs lptos rptos fpptos = *)
(*   let truef = Cpure.mkTrue no_pos in *)
(*   let lp = List.fold_left (fun acc_p (sv1, sv2) -> *)
(*       let p = CP.mkEqExp (Exp.mkVar sv1 no_pos) *)
(*         (Exp.mkVar sv2 no_pos) no_pos in *)
(*         CP.mkAnd acc_p p no_pos *)
(*   ) truef lneqs in *)
(*   (* RHS: context sensitive-unfolding (or view-pruning) *) *)
(*     let runfold_lbls_list = search_ctx_unfold cpreds rvns lp reqNulls reqs rneqs (rptos@fpptos) in *)
(*     if runfold_lbls_list !=[] then *)
(*       (*TODO: unfold all*) *)
(*       let runfold_lbls = List.hd runfold_lbls_list in *)
(*       let r= proof_search_unfold cpreds e false runfold_lbls in *)
(*       true, (List.map (fun a -> [a]) r,[], ENorm) *)
(*     else *)
(*   (* LHS *) *)
(*   let lunfold_lbls_list = search_ctx_unfold cpreds lvns lp leqNulls leqs lneqs (lptos@fpptos) in *)
(*   if lunfold_lbls_list !=[] then *)
(*     (*TODO: unfold all*) *)
(*     let lunfold_lbls = List.hd lunfold_lbls_list in *)
(*     let r= proof_search_unfold cpreds e true lunfold_lbls in *)
(*     true, ([r],[],ENorm) *)
(*   else *)
(*     false, ([], [], ENorm) *)

(*is it indr?*)
(* let ps_is_exed_mid cpreds e l_nulls ldisnulls lneqs vn r_nulls = *)
(*   let srcs, tars = Cpred.get_src_tar_acyclic cpreds vn.PeN.hpred_name vn.PeN.hpred_arguments in *)
(*   match srcs, tars with *)
(*     | s::_,t::_ -> begin *)
(*         match (check_excluded [s] [t] lneqs) with *)
(*           | Some (s,t) -> false *)
(*           | None -> true *)
(*       end *)
(*     | _ -> false *)

let ps_ex_mid cpreds is_left e l_nulls ldisnulls lneqs vn r_nulls =
  let srcs, tars = Cpred.get_root_src_tar_acyclic cpreds vn.PeN.hpred_name vn.PeN.hpred_arguments in
  match srcs, tars with
    | s::_,t::_ -> begin
        if (not is_left && Var.mem t (r_nulls@l_nulls))  then
          if Var.mem s (l_nulls@ldisnulls) then
            None
          else Some (ps_exclude_middle cpreds (s,t) is_left vn e)
        else
          let r =
            match (check_excluded [s] [t] lneqs) with
              | Some (s,t) ->
                    Some (ps_exclude_middle cpreds (s,t) is_left vn e)
              | None -> None
          in r
      end
    | _ -> None

let do_right_unfold cpreds e ldiseqs rdiseqs l_allocas l_nulls r_nulls runfold_lbls=
  let rbrs = proof_search_unfold cpreds e false ldiseqs rdiseqs l_allocas l_nulls r_nulls runfold_lbls  in
  if rbrs ==[] then ([],[],  ERuEmp)
  else
    (* clone mutiple trees. eliminate a search if its RHS contradicts with LHS *)
    let r2 = List.map (fun r -> [r]) rbrs (* proof_search_right_linear_unfold_filter rbrs (ldiseqs@rdiseqs) *) in
    (r2, [], ENorm)

let do_left_unfold cpreds e ldiseqs rdiseqs l_allocas l_nulls r_nulls lunfold_lbls=
  let r= proof_search_unfold cpreds e true ldiseqs rdiseqs l_allocas l_nulls r_nulls lunfold_lbls in
  let status = if r==[] then ELuEmp else ENorm in
  ([r], [], status)

let left_unfold_fresh_cyclic cpreds e ldiseqs rdiseqs l_allocas l_nulls r_nulls lvns=
  try
    let lvn = List.find (fun vn ->
        if vn.PeN.hpred_unfold_num == 0 then
           let d = List.find (fun decl -> Ustr.str_eq vn.PeN.hpred_name decl.Cpred.pred_name) cpreds in
           not d.Cpred.pred_is_acyclic
        else false
        ) lvns in
    let lunfold_lbls = unfold_pred cpreds lvn in
    do_left_unfold cpreds e ldiseqs rdiseqs l_allocas l_nulls r_nulls lunfold_lbls
  with Not_found -> [], [], ENorm

let do_base_linear_unfold cpreds e is_left lneqs rneqs l_allocas l_nulls r_nulls lunfold_lbls=
  let r = proof_search_unfold ~ctx_pruning:false cpreds e is_left lneqs rneqs l_allocas l_nulls r_nulls lunfold_lbls in
  r

let do_base_case_unfold_cyclic cpreds e is_left lneqs rneqs l_allocas l_nulls r_nulls rvns fpvns fp_allocas=
  try
  let fp_srcs = List.map (fun vn ->
      Cpred.get_root_src_composition cpreds vn.PeN.hpred_name vn.PeN.hpred_arguments
  ) fpvns in
  if List.exists (fun rvn -> begin
    let d = List.find (fun decl -> Ustr.str_eq rvn.PeN.hpred_name decl.Cpred.pred_name) cpreds in
    if not d.Cpred.pred_is_acyclic then false else
      match d.Cpred.pred_composition_vars with
        | Some ((ls, _, _, _, _, _), _) ->
              let sst = List.combine d.Cpred.pred_vars rvn.PeN.hpred_arguments in
              let srcs= List.fold_left (fun r (sv,_) -> r@[(Var.subst sst sv)]) [] ls in
              List.exists (fun v -> Var.mem v fp_allocas) srcs ||
                  List.exists (fun f_scrcs -> List.exists (fun v -> Var.mem v f_scrcs) srcs) fp_srcs
        | None -> false
  end
  ) rvns then
    [],[], ESNoRule
  else
    let is_rhs_empty_heap, ls_runfolds = Cpred.search_unfold_emp_branch cpreds rvns in
    if not is_rhs_empty_heap then [],[], ESNoRule
    else (* do unfold all runfolds *)
      let searches = proof_search_unfold_seq ~ctx_pruning:false cpreds e is_left lneqs rneqs l_allocas l_nulls r_nulls ls_runfolds in
      if searches == [] then [], [], ERuEmp
      else
        let r = List.map (fun r -> [r]) searches in
        r,[],ENorm
  with Not_found ->
      [],[], ESNoRule

let is_composable cpreds lvn rvn fp_allocas l_allocas l_nulls r_nulls=
  let is_match_src_local_vars largs rargs (ext_prs, precise_prs) formal_args=
    if ext_prs== [] && precise_prs == [] then [],[]
    else
      let lsst = List.combine formal_args largs in
      let rsst = List.combine formal_args rargs in
      let ext_sst = List.fold_left (fun r (sv, _) ->
          let larg = (Var.subst lsst sv) in
          let rarg =  (Var.subst rsst sv) in
          if Var.equal larg rarg then r
          else r@[(rarg,larg)]
      ) [] ext_prs in
      let precise_sst = List.fold_left (fun r (sv, _) ->
          let larg = (Var.subst lsst sv) in
          let rarg =  (Var.subst rsst sv) in
          if Var.equal larg rarg then r
          else r@[(rarg,larg)]
      ) [] precise_prs in
      (ext_sst, precise_sst)
  in
  try
  let d = List.find (fun decl -> Ustr.str_eq rvn.PeN.hpred_name decl.Cpred.pred_name) cpreds in
  if (d.Cpred.pred_compose_rule_same_ext_src) != [] || d.Cpred.pred_compose_rule_diff_ext_src != [] then
    let () = Debug.ninfo_hprint (add_str "ln1" (PeN.string_of)) lvn no_pos in
    let () = Debug.ninfo_hprint (add_str "rn1" (PeN.string_of)) rvn no_pos in
    match d.Cpred.pred_composition_vars with
      | Some ((root_prs, local_precise_prs, local_ext_prs, non_precise_prs, nonlocal_ext_prs, _), _) -> begin
          (*to apply composition rule, all local srcs must be matched between two sides*)
          let (* is_root_match, *) cond_inst_ext_sst, cond_inst_precise_sst = (is_match_src_local_vars lvn.PeN.hpred_arguments
                rvn.PeN.hpred_arguments ((* List.map fst root_prs, *) local_ext_prs@nonlocal_ext_prs, local_precise_prs@non_precise_prs) d.Cpred.pred_vars) in
          (* if not is_root_match then false, ([], []) else *)
            if cond_inst_ext_sst!=[] || cond_inst_precise_sst!=[] then true, (cond_inst_ext_sst, cond_inst_precise_sst)
            else if not d.Cpred.pred_is_acyclic then true, ([],[])
            else
              let sst = List.combine d.Cpred.pred_vars rvn.PeN.hpred_arguments in
              let tars = List.fold_left (fun r (_, sv) -> r@[Var.subst sst sv]) [] root_prs in
              let () = Debug.ninfo_hprint (add_str "tars" (Var.string_of_list)) tars no_pos in
              let () = Debug.ninfo_hprint (add_str "fp_allocas" (Var.string_of_list)) fp_allocas no_pos in
              let allocated_svs = (fp_allocas@l_allocas@l_nulls@r_nulls) in
              let () = Debug.ninfo_hprint (add_str "allocated_svs" (Var.string_of_list)) allocated_svs no_pos in
              List.exists (fun sv1 -> List.exists (fun sv2 -> Var.equal sv1 sv2) allocated_svs) tars, ([],[])
        end
      | None -> false, ([], [])
  else false, ([], [])
with Not_found -> false, ([], [])

let ps_composition_linear_pred cpreds e lvn lptos leqs ldiseqs rdiseqs l_nulls rvn reqs r_nulls
      l_allocas fpvns fp_allocas=
  (* if predicate is compositional and flag is true: apply with composition_rule *)
  let ls_composes = proof_search_composition_right_unfold cpreds e (lvn, rvn) in
  List.map (fun r -> [r]) ls_composes, [], ENorm

let ps_pred_pred cpreds e cyc_matched_preds lvns lptos leqs ldiseqs rdiseqs l_nulls rvns reqs  r_nulls rqvars
      l_allocas fpvns fp_allocas=
  (* match root of diff preds *)
  let m_preds0 = if cyc_matched_preds != [] then cyc_matched_preds else find_pred_root_match cpreds true lvns leqs rvns reqs in
  (* give higher priority for the starting pointers *)
  let next_ptrs = List.fold_left (fun r pto -> r@pto.PoN.hpto_arguments) [] lptos in
  let m_preds,rest = List.partition (fun (ln,_) ->
      let srcs = Cpred.get_root_src_composition cpreds ln.PeN.hpred_name ln.PeN.hpred_arguments in
      Var.intersect srcs next_ptrs == []
  ) m_preds0 in
  let m_preds1 = m_preds@rest in
  let m_same_preds, m_diff_preds = List.partition (fun (ln, rn) ->
  Ustr.str_eq ln.PeN.hpred_name rn.PeN.hpred_name ) m_preds1 in
  match m_same_preds with
    | (lvn,rvn)::_ -> begin
        (* let () = Debug.info_hprint (add_str "pred_root_match rvn" (PeN.string_of)) rvn no_pos in *)
        (* try begin *)
          (* ls(x1,x2) |- ls(x1,x3)
             only unfold LHS  if x3|->_ or x3=null in either LHS or footprint, src *)
          (* let (lvn,rvn) = List.find (fun (ln1,rn1) -> *)
        let is_ok, (cond_ext_sst, cond_precise_sst) = is_composable cpreds lvn rvn fp_allocas l_allocas l_nulls r_nulls in
        if is_ok then
          let ex_cond_precise_sst, neq_precise_sst = List.partition (fun (rv, _) -> Var.mem rv rqvars) cond_precise_sst in
          if neq_precise_sst != []  then
            let r= proof_search_left_unfold_pred cpreds e lvn leqs ldiseqs rdiseqs l_allocas l_nulls r_nulls in
            true, r
          else
            let ex_cond_ext_sst = List.filter (fun (rv, _) -> Var.mem rv rqvars) cond_ext_sst in
            let ex_cond_sst = ex_cond_precise_sst@ex_cond_ext_sst in
            if ex_cond_sst ==[] then
              true, ps_composition_linear_pred cpreds e lvn lptos leqs ldiseqs rdiseqs l_nulls rvn reqs r_nulls
                  l_allocas fpvns fp_allocas
            else
              (*to check condition: all RHS vars are quantified *)
              let r =  ps_rhs_instantiate cpreds e ex_cond_sst in
                true, ([r], [], ENorm)
        else
          (* ) m_preds1 in *)
          (*   (\*TODO: same pred -> big-step unfold*\) *)
          (*   (\* small-step unfold *\) *)
          let r= proof_search_left_unfold_pred cpreds e lvn leqs ldiseqs rdiseqs l_allocas l_nulls r_nulls in
          true, r
              (* end *)
              (* with Not_found -> *)
              (* STUCK DANGLING: only apply when in NF*)
              (* true, ([], [], ESDangl) *)
      end
    | [] -> begin
        match m_diff_preds with
          | (lvn,rvn)::_ -> let r= proof_search_left_unfold_pred cpreds e lvn leqs ldiseqs rdiseqs l_allocas l_nulls r_nulls in
            true, r
          | [] -> false, ([], [], ESNoRule)
      end

let ps_pred_root_unfold cpreds e lvns rvns leqs reqs ldiseqs rdiseqs l_allocas l_nulls r_nulls root=
  let lunfold_lbls, _ =
    try
      search_pred_with_match_alloca cpreds false lvns leqs [root]
    with Not_found -> [],[]
  in
  if lunfold_lbls != [] then
    true, do_left_unfold cpreds e ldiseqs rdiseqs l_allocas l_nulls r_nulls lunfold_lbls
  else
    let runfold_lbls, _ =
      try
        search_pred_with_match_alloca cpreds false rvns (leqs@reqs) [root]
      with Not_found -> [],[]
    in
    if runfold_lbls != [] then
      true, do_right_unfold cpreds e ldiseqs rdiseqs l_allocas l_nulls r_nulls runfold_lbls
    else
      false, ([],[],ENorm)


let ps_col_x cpreds is_ho e =
  let _, lbare = SLND.split_quantifiers e.ENT.ante in
  let _, rbare = SLND.split_quantifiers e.ENT.cons in
  let lqvars0, lvns, lptos, leql,_ = SLN.star_decompose e.ENT.ante in
  let rqvars0, rvns, rptos, reql,_ = SLN.star_decompose e.ENT.cons in
  (* let lp = SLND.to_pure e.ENT.ante in *)
  (* let rp = SLND.to_pure e.ENT.cons in *)
  let leqNulls, ldisnulls, leqs, lneqs = EQ.decompose leql in
  let reqNulls, _, reqs, rneqs =  EQ.decompose reql in
  let fpvns, fpptos = CH.star_decompose e.ENT.fp in
  let fp_allocas = Var.get_eq_closure leqs (List.map (fun n -> n.PoN.hpto_node) fpptos) in
  (* let b1, r = ps_ctx_unfold cpreds e lvns rvns leqNulls reqNulls leqs reqs lneqs rneqs lptos rptos fpptos in *)
  (* if b1 then r else *)
  (* **** %%%%%%%%** match points-to %%%%%%%%*)
  (* matching free point-to predicates *)
  let q_lptos, qf_lptos = List.partition (fun n ->
      let pts = Var.get_eq_closure leqs [n.PoN.hpto_node] in
      Var.diff pts  lqvars0 == []) lptos in
  let q_rptos, qf_rptos = List.partition (fun n ->
      let pts = Var.get_eq_closure (leqs@reqs) [n.PoN.hpto_node] in
      Var.diff pts rqvars0 == []) rptos in
  let l_allocas = Var.get_eq_closure leqs (List.map (fun n -> n.PoN.hpto_node) qf_lptos) in
  let l_nulls = Var.get_eq_closure leqs leqNulls in
  let r_allocas = Var.get_eq_closure reqs (List.map (fun n -> n.PoN.hpto_node) qf_rptos) in
  let r_nulls = Var.get_eq_closure reqs reqNulls in
  let () = Debug.ninfo_hprint (add_str "l_nulls" (Var.string_of_list)) l_nulls no_pos in
  let m_ptos = find_pto_match qf_lptos qf_rptos leqs reqs in
  (*TODO: check stuck RInd here *)
  match m_ptos with
    | (ln,rn)::_ ->
          (* remove STUCK: RInd. unfold predicate in LHS and RHS
             if it has the same root *)
          let is_ok1, r = ps_pred_root_unfold cpreds e lvns rvns leqs reqs lneqs rneqs l_allocas l_nulls r_nulls ln.PoN.hpto_node in
          if is_ok1 then r else begin
            try
              let r, sst = proof_search_match_point_to cpreds e (ln,rn) lqvars0 lbare rqvars0 rbare in
              [r], sst, ENorm
            with _ -> [],[], EPtoNoMatch
          end
    | [] -> begin (* BEGIN: not any matched ptos *)
        (*match preds *)
        let m_acpreds, m_cpreds, m_cpreds_end = find_pred_match cpreds lvns lqvars0 leqs l_nulls rvns rqvars0 reqs r_nulls in
        (*TODO: check stuck LInd here *)
        match (m_acpreds@m_cpreds_end) with
            | (ln,rn)::_ -> begin
                (* if ps_is_exed_mid cpreds e l_nulls ldisnulls lneqs ln r_nulls then *)
                (*   (\*it is ind. unfold it to exclude the middle*\) *)
                (*   proof_search_left_unfold_pred cpreds e ln leqs lneqs rneqs l_allocas l_nulls r_nulls *)
                (* else *)
                  (*TODO: postpone EX-MID to
                    check sat of fp in case of invalid *)
                  let r = proof_search_match_pred_cond cpreds e (ln,rn) leqs reqs
                  in [r],[],ENorm
              end
            | [] -> begin (* BEGIN: not any matched pred *)
                (* unfold  base case lhs *)
                let lunfold_lbls = Cpred.search_pred_base_linear_unfold cpreds lvns leqs (l_nulls) (* search_pred_base_case cpreds lvn *) in
                if lunfold_lbls !=[] then
                  let lbrs = do_base_linear_unfold cpreds e true lneqs rneqs l_allocas l_nulls r_nulls lunfold_lbls in
                  if lbrs == [] then [], [], ELuEmp
                  else [lbrs],[],ENorm
                else
                (* unfold  base case rhs *)
                let runfold_lbls = Cpred.search_pred_base_linear_unfold cpreds rvns reqs (l_nulls@r_nulls) in
                if runfold_lbls != [] then
                  let rbrs =  do_base_linear_unfold cpreds e false lneqs rneqs l_allocas l_nulls r_nulls runfold_lbls in
                  (* to clone mutiple trees *)
                  if rbrs == [] then [], [], ERuEmp
                  else
                    let r = List.map (fun r -> [r]) rbrs (* proof_search_right_linear_unfold_filter rbrs (lneqs@rneqs) *) in
                    r,[],ENorm
                else begin
                  try
                    (* EX-MID + RInd *)
                    (* (x|->.. <-> Q(x,..)) *)
                    let runfold_lbls, src_tars = search_pred_with_match_alloca cpreds false rvns reqs (l_allocas@l_nulls) in
                    let (rn, _ ) = List.hd runfold_lbls in
                    match ps_ex_mid cpreds false e l_nulls ldisnulls lneqs rn r_nulls with
                      | Some r -> [r],[],ENorm
                      | None ->
                            do_right_unfold cpreds e  (lneqs) rneqs l_allocas l_nulls r_nulls runfold_lbls
                  with Not_found -> begin
                    (* EX+COMPOSE (P(x,..) <->Q(x...) *)
                    let q_rallocals = List.map (fun n -> n.PoN.hpto_node) q_rptos in
                    let is_applied, r = ps_pred_pred cpreds e m_cpreds lvns lptos leqs lneqs rneqs l_nulls rvns reqs r_nulls (Var.diff rqvars0 q_rallocals)
                        l_allocas fpvns fp_allocas in
                    if is_applied then r else
                      (* let lr = proof_search_unfold_dupl_roots ~ctx_pruning:true cpreds e true lneqs rneqs l_allocas l_nulls r_nulls fpvns fp_allocas lvns in *)
                      (* if lr !=[] then [lr], [], ENorm *)
                      (* else *)
                      (* empty heap in LHS? *)
                      if lvns==[] && lptos==[] then
                        do_base_case_unfold_cyclic cpreds e false lneqs rneqs l_allocas l_nulls r_nulls rvns fpvns fp_allocas
                      else
                        if rvns==[] && rptos==[] then
                          (* unfold fresh vns: with unfolding number = 0*)
                          let lr, sst, s = left_unfold_fresh_cyclic cpreds e lneqs rneqs l_allocas l_nulls r_nulls lvns in
                          if lr != [] then lr, sst, s
                          else [],[], ESNoRule
                        else
                        (*   let rr = proof_search_unfold_dupl_roots ~ctx_pruning:true cpreds e false lneqs rneqs r_allocas l_nulls r_nulls fpvns fp_allocas rvns in *)
                        (*   if rr != [] then *)
                        (*     List.map (fun r -> [r]) rr, [], ENorm *)
                        (*   else *) [],[], ESNoRule
                  end (* END: EX +COMPOSE *)
                end
              end (* END: empty match pred *)
      end (* END: empty match ptos *)


let ps_col cpreds is_ho e=
  let pr1 = ENT.string_of_short in
  let pr2 = pr_list_ln (pr_pair pr1 string_of) in
  let pr_out = pr_triple (pr_list_ln pr2) (pr_list Var.string_of_pair) Com.string_of_entstuck in
  Debug.no_1 "ps_col" pr1 pr_out
      (fun _ -> ps_col_x cpreds is_ho e) e
