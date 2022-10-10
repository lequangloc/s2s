open Globals
open Gen.Basic
open VarGen
open Gen

module CF = Cformula
module CP = Cpure
module PeN = CpredNode
module PoN = CptoNode
module CoRule = CcoRule

type pred_decl =
  {
    pred_name : ident;
    pred_vars : Var.t list;
    mutable pred_formula : Cformula.t;
    mutable pred_pure_inv : CP.formula;
    mutable pred_base : Cformula.t list * Cformula.t list;

    pred_unfolded_formula : Cformula.t list;
    pred_formula_w_ctx : (Cpure.t * Cformula.t) list;

    pred_rec : rec_kind;
    mutable pred_is_sat_deci : bool;
    pred_is_ent_deci : bool;
    pred_is_shape_only : bool;
    mutable pred_is_ent_base_reused : bool;
    pred_is_acyclic : bool; (*linear and acyclic*)
    pred_is_pure_acyclic : bool list;
    pred_is_composable : bool; (*possible to apply composition rule*)
    mutable pred_compose_rule_same_ext_src: CoRule.t list;
    mutable pred_compose_rule_diff_ext_src: CoRule.t list;
    mutable pred_strengthen_rules: StreRule.t list;
    pred_is_pure : bool;


    (* precise pred *)
    (* pred_order: int; *)
    pred_roots: Var.t list;
    pred_composition_vars: (((Var.t * Var.t) list * (Var.t * Var.t) list * (Var.t * Var.t) list *
         (Var.t * Var.t) list * (Var.t * Var.t) list  * Var.t list)
        * ((Var.t * Var.t) list))
        option;
        (* spatial (source * target) list * local cyclic  (source * target) list
         * local acyclic  (source * target) list * non-local acylic (source * target) list * boundary list
         * (disjoint_prs)
         *)
    pred_bw_tars: Var.t list;

    pred_is_prim : bool;
    pred_data_name : ident;
    pred_parent_name: (ident) option;

    pred_pos : loc;
  }

type t = pred_decl


let string_of v = "\npred " ^ v.pred_name ^ "< " ^
  (String.concat "," (List.map Var.string_of v.pred_vars)) ^ "> == " ^
  (CF.string_of v.pred_formula) ^
  "\n inv " ^ (CP.string_of v.pred_pure_inv) ^ "." ^
  "\n roots: " ^ (Var.string_of_list v.pred_roots) ^
  "\n composition_vars: " ^ ((pr_option (pr_pair (pr_hexa (pr_list Var.string_of_pair) (pr_list Var.string_of_pair) (pr_list Var.string_of_pair)
      (pr_list Var.string_of_pair) (pr_list Var.string_of_pair) Var.string_of_list) (pr_list Var.string_of_pair))) v.pred_composition_vars) ^"." ^
  "\n bw vars: " ^ ( Var.string_of_list v.pred_bw_tars) ^"." ^
  "\n pred_unfolded_formula " ^ ((pr_list CF.string_of) v.pred_unfolded_formula) ^ "." ^
  "\n bases " ^ ((pr_list_ln CF.string_of) (fst v.pred_base)) ^ "." ^
  "\n buds " ^ ((pr_list_ln CF.string_of) (snd v.pred_base)) ^ "." ^
  "\n[" ^ (string_of_rec_kind v.pred_rec) ^ "; sat deci:" ^
  (string_of_bool v.pred_is_sat_deci) ^ "; ent deci:" ^
  (string_of_bool v.pred_is_ent_deci) ^ "; shape only:" ^
  (string_of_bool v.pred_is_shape_only) ^ "; ent_base_reused:" ^
  (string_of_bool v.pred_is_ent_base_reused) ^ "; is_linear_acyclic:" ^ (string_of_bool v.pred_is_acyclic) ^
   "; is_pure_linear_acyclic:" ^ ((pr_list string_of_bool) v.pred_is_pure_acyclic) ^
   "; pred_is_composable:" ^ (string_of_bool v.pred_is_composable) ^ "]" ^
"\nCompose Rule (same): " ^ ((pr_list_ln CoRule.string_of) v.pred_compose_rule_same_ext_src)
^
"\nCompose Rule (diff): " ^ ((pr_list_ln CoRule.string_of) v.pred_compose_rule_diff_ext_src) ^
  "\nStrengthen Rules: " ^ ((pr_list_ln StreRule.string_of) v.pred_strengthen_rules)

let get_pred_all_inv preds=
  List.fold_left (fun r vdcl ->
      if Cpure.isTrue vdcl.pred_pure_inv then r
        else
          r@[(vdcl.pred_name, (vdcl.pred_vars,  vdcl.pred_pure_inv))]
    ) [] preds

let get_pred_inv pdecls vn args=
  try
    let pdecl = List.find (fun decl ->
        Ustr.str_eq vn decl.pred_name) pdecls in
    let sst = List.combine pdecl.pred_vars args in
    CP.subst_var sst (CP.fresh_quantifiers pdecl.pred_pure_inv)
  with Not_found -> CP.mkTrue no_pos

let safe_unfold_num cpreds vn=
  let decl = List.find (fun p ->
      Ustr.str_eq vn p.pred_name
  ) cpreds in
  let num_try = match decl.pred_rec with
    | NOREC -> 1
    | SELFREC -> 1
    | MUTREC ls -> List.length ls
  in num_try

let get_root_src_tar_acyclic_x cpreds vn act_args=
  try
    let d = List.find (fun decl -> Ustr.str_eq vn decl.pred_name) cpreds in
    if not d.pred_is_acyclic then [], [] else
      match d.pred_composition_vars with
        | Some ((prs, _, _, _, _, _), _) ->
              if prs==[] then [],[] else
              let sst = List.combine d.pred_vars act_args in
                let n_prs = List.map (fun (sv1, sv2) -> (Var.subst sst sv1, Var.subst sst sv2) ) prs in
                List.split n_prs
                (* ([(Var.subst sst src)], [(Var.subst sst tar)]) *)
        | None -> [],[]
  with Not_found -> [], []

let get_root_src_tar_acyclic cpreds vn act_args=
  let pr2 = Var.string_of_list in
  let pr_out = pr_pair pr2 pr2 in
  Debug.no_3 "get_root_src_tar_acyclic" (pr_list_ln string_of)
      pr_id pr2 pr_out
      (fun _ _ _ -> get_root_src_tar_acyclic_x cpreds vn act_args)
      cpreds vn act_args

let get_root_src_tar_composition cpreds vn act_args=
  try
    let d = List.find (fun decl -> Ustr.str_eq vn decl.pred_name) cpreds in
    match d.pred_composition_vars with
      | Some ((prs, _, _, _, _, _), _) ->
            if prs ==[] then [],[] else
            let sst = List.combine d.pred_vars act_args in
            let n_prs = List.map (fun (sv1, sv2) -> (Var.subst sst sv1, Var.subst sst sv2) ) prs in
            List.split n_prs
      | None -> [],[]
  with Not_found -> [], []

let get_all_src_tar_composition cpreds vn act_args=
  try
    let d = List.find (fun decl -> Ustr.str_eq vn decl.pred_name) cpreds in
    match d.pred_composition_vars with
      | Some ((root_prs, cyc_prs, acyc_local_prs, non_local_prs, non_local_ext_prs, others), _) ->
            if root_prs ==[] then [],[],[],[],[],[],[],[], [], [], [] else
            let sst = List.combine d.pred_vars act_args in
            let n_root_prs = List.map (fun (sv1, sv2) -> (Var.subst sst sv1, Var.subst sst sv2) ) (root_prs) in
            let n_cyc_prs = List.map (fun (sv1, sv2) -> (Var.subst sst sv1, Var.subst sst sv2) ) (cyc_prs) in
            let n_acyc_prs = List.map (fun (sv1, sv2) -> (Var.subst sst sv1, Var.subst sst sv2) ) (acyc_local_prs) in
            let n_non_prs = List.map (fun (sv1, sv2) -> (Var.subst sst sv1, Var.subst sst sv2) ) (non_local_prs) in
            let n_non_ext_prs = List.map (fun (sv1, sv2) -> (Var.subst sst sv1, Var.subst sst sv2) ) (non_local_ext_prs) in
            let root_srcs, root_tars = List.split n_root_prs in
            let cyc_srcs, cyc_tars = List.split n_cyc_prs in
            let acyc_srcs, acyc_tars = List.split n_acyc_prs in
            let non_srcs, non_tars = List.split n_non_prs in
            let non_ext_srcs, non_ext_tars = List.split n_non_ext_prs in
            let n_others = List.map (Var.subst sst) others in
            (root_srcs, root_tars, cyc_srcs, cyc_tars, acyc_srcs, acyc_tars , non_srcs, non_tars, non_ext_srcs, non_ext_tars, n_others)
      | None -> [],[], [], [], [],[],[],[], [], [], []
  with Not_found -> [], [], [], [],[],[],[],[], [], [], []

let get_root_src_composition cpreds vn act_args=
  try
    let d = List.find (fun decl -> Ustr.str_eq vn decl.pred_name) cpreds in
    match d.pred_composition_vars with
        | Some ((prs, _, _, _ ,_, _), _) -> if prs ==[] then [] else
            let sst = List.combine d.pred_vars act_args in
            List.fold_left (fun r (sv1, _) -> r@[(Var.subst sst sv1)]) [] prs
        | None -> []
  with Not_found -> []

let get_root_tar_composition cpreds vn act_args=
  try
    let d = List.find (fun decl -> Ustr.str_eq vn decl.pred_name) cpreds in
    match d.pred_composition_vars with
        | Some (( prs, _, _, _, _, _), _) -> if prs ==[] then (false, []) else
            let sst = List.combine d.pred_vars act_args in
            d.pred_is_acyclic, List.fold_left (fun r (_, sv1) -> r@[(Var.subst sst sv1)]) [] prs
        | None ->  false, []
  with Not_found -> false, []

let  is_pred_acyclic cpreds vn=
  try
    let d = List.find (fun decl -> Ustr.str_eq vn decl.pred_name) cpreds in
    d.pred_is_acyclic
  with Not_found -> false

(*
  find a predicate occurence in LHS such that
its src parameter are points-to predicates in RHS
*)

let extract_roots cpreds vn=
  try
     let pdecl = List.find (fun pd -> Ustr.str_eq vn.PeN.hpred_name pd.pred_name) cpreds in
     match pdecl.pred_composition_vars with
       | Some ((ls, _, _, _, _, _), _) -> begin
           let rs = match ls with
             | (s,_)::_ -> pdecl.pred_roots@[s]
             | _ -> pdecl.pred_roots
           in
           let sst = List.combine pdecl.pred_vars vn.PeN.hpred_arguments in
           List.map (Var.subst sst) rs
         end
       | None ->
             []
  with Not_found -> []



let get_composition_rule_x cpreds vn
      root_args1 precise_args1 ext_largs1 nl_ext_largs1
      ext_rargs1 nl_ext_rargs1
      other_args1
      root_args2 precise_args2 ext_args2 nl_precise_args2 nl_ext_args2
      root_args3 precise_args3 ext_args3 nl_precise_args3 nl_ext_args3
      other_args3  =
  let aux_rule is_same_ext_src corule=
    begin
      let sst0 = if is_same_ext_src then [] else
        (* for diff lemma *)
        List.combine (corule.CoRule.colem_root_args1@corule.CoRule.colem_precise_args1@corule.CoRule.colem_ext_largs1@corule.CoRule.colem_nl_ext_largs1@corule.CoRule.colem_ext_rargs1@corule.CoRule.colem_nl_ext_rargs1)
        (root_args1@precise_args1@ext_largs1@nl_ext_largs1@ext_rargs1@nl_ext_rargs1) in
      let sst1 = List.combine (corule.CoRule.colem_root_args2@corule.CoRule.colem_precise_args2@corule.CoRule.colem_ext_args2@corule.CoRule.colem_nl_precise_args2@corule.CoRule.colem_nl_ext_args2) (root_args2@precise_args2@ext_args2@nl_precise_args2@nl_ext_args2) in
      let sst2 = List.combine (corule.CoRule.colem_root_args3@corule.CoRule.colem_precise_args3@corule.CoRule.colem_ext_args3@corule.CoRule.colem_nl_precise_args3@corule.CoRule.colem_nl_ext_args3) (root_args3@precise_args3@ext_args3@nl_precise_args3@nl_ext_args3) in
      let qvars = List.map Var.fresh_var corule.CoRule.colem_qvars in
      let sst3 = List.combine corule.CoRule.colem_qvars qvars in
      let sst = (sst0@sst1@sst2@sst3) in
      let lhs_sst_pure = List.combine corule.CoRule.colem_other_args1 other_args1 in
      let rhs_sst_pure = List.combine corule.CoRule.colem_other_args3 other_args3 in
      qvars, List.map (PeN.subst sst) corule.CoRule.colem_rem,
      Cpure.subst_var (sst@lhs_sst_pure@rhs_sst_pure) corule.CoRule.colem_pure
    end
  in
  let cpred = List.find (fun decl -> Ustr.str_eq vn decl.pred_name) cpreds in
  let is_same_ext_src = List.for_all (fun (lv, rv) ->
      Var.equal lv rv
  ) (List.combine (ext_largs1@nl_ext_largs1) (ext_rargs1@nl_ext_rargs1))in
  let formal_rules = if is_same_ext_src then
    cpred.pred_compose_rule_same_ext_src
  else
    cpred.pred_compose_rule_diff_ext_src
  in
  let actual_rules = List.map (fun r -> aux_rule is_same_ext_src r)
    formal_rules in
  actual_rules

let get_composition_rule cpreds vn
      root_args1 precise_args1 ext_largs1 nl_ext_largs1
      ext_rargs1 nl_ext_rargs1
      other_args1
      root_args2 precise_args2 ext_args2 nl_precise_args2 nl_ext_args2
      root_args3 precise_args3 ext_args3 nl_precise_args3 nl_ext_args3
      other_args3  =
  let pr1 = Var.string_of_list in
  let pr_out = pr_triple pr1 (pr_list PeN.string_of) Cpure.string_of in
  Debug.no_4 "get_composition_rule" pr1 pr1 pr1 pr1 (pr_list_ln pr_out)
      (fun _ _ _ _ -> get_composition_rule_x cpreds vn
          root_args1 precise_args1 ext_largs1 nl_ext_largs1
      ext_rargs1 nl_ext_rargs1
          other_args1
          root_args2 precise_args2 ext_args2 nl_precise_args2 nl_ext_args2
          root_args3 precise_args3 ext_args3 nl_precise_args3 nl_ext_args3
          other_args3)
      (root_args2@precise_args2) (ext_args2@nl_precise_args2)
      (root_args3@precise_args3) (ext_args3@nl_precise_args3)

let get_strengthen_rules_x cpreds vn args=
  let process_one srule=
    let sst = List.combine srule.StreRule.strelem_args args in
    PeN.subst sst srule.StreRule.strelem_heap
  in
  let p = List.find (fun decl -> Ustr.str_eq vn decl.pred_name) cpreds in
  if p.pred_strengthen_rules == [] then [] else
    try
      List.map process_one p.pred_strengthen_rules
    with _ -> []

let get_strengthen_rules cpreds vn args=
  let pr1 = pr_list PeN.string_of in
  Debug.no_2 "get_strengthen_rules" pr_id Var.string_of_list pr1
      (fun _ _ -> get_strengthen_rules_x cpreds vn args) vn args

let search_pred_base_linear_unfold_x cpreds vns0 eqs nulls=
  let base_case_unfold_acycli_pure vn pdecl sst acyc_prs =
    (* let acyc_prs = List.fold_left (fun r (pr, b) -> *)
    (*     if b then r@[pr] else r *)
    (* ) [] (List.combine lprs pdecl.pred_is_pure_acyclic) in *)
    if acyc_prs ==[] then
      []
    else
      let base_acyc_prs =List.fold_left (fun r  (v1, v2) ->
          let v11 = Var.subst sst v1 in
          let v21 = Var.subst sst v2 in
          if Var.equal v11 v21 ||
              (Var.mem v11 nulls && Var.mem v21 nulls)
          then r@[(v11, v21)]
          else r
      ) [] acyc_prs in
      if base_acyc_prs == [] then [] else
        List.fold_left (fun r f -> begin
          if CF.isEmptyHeap f then r@[(vn, f)]
            else r
        end
        ) [] (CF.list_of_disjuncts (CF.subst sst pdecl.pred_formula))
  in
  let rec aux vns= match vns with
    | vn::rest -> begin
        try
          let pdecl = List.find (fun pd -> Ustr.str_eq vn.PeN.hpred_name pd.pred_name) cpreds in
          let roots, src_tars, dis_prs =  match pdecl.pred_composition_vars with
              | Some ((prs, _, _, _, _, _), dis_prs) ->
                    pdecl.pred_roots, prs, dis_prs
              | None -> [], [], []
          in
          if roots == [] && src_tars == [] then []
          else
            (* let () = Debug.info_hprint (add_str  "pdecl.pred_vars" (Var.string_of_list)) pdecl.pred_vars no_pos in *)
            (* let () = Debug.info_hprint (add_str  "vn.PeN.hpred_arguments" (Var.string_of_list)) vn.PeN.hpred_arguments no_pos in *)
            let sst = List.combine pdecl.pred_vars vn.PeN.hpred_arguments in
            let roots1 = Var.get_eq_closure eqs (List.map (Var.subst sst) roots) in
            let roots2 = Var.intersect roots1 nulls in
            let fs = if roots2 != [] then
              List.fold_left (fun r f -> let _, ptos = CF.star_decompose f in
              if List.exists (fun dn -> List.mem dn.PoN.hpto_node roots2) ptos then r
              else r@[(vn, f)]) [] (CF.list_of_disjuncts
                  (CF.subst sst pdecl.pred_formula))
            else if not pdecl.pred_is_acyclic then base_case_unfold_acycli_pure vn pdecl sst dis_prs
            else
              match src_tars with
                | (s, t)::_ ->
                      let s1 = (Var.subst sst s) in
                      let t1 = (Var.subst sst t) in
                      let ss = Var.get_eq_closure eqs [s1] in
                      let ts = Var.get_eq_closure eqs [t1] in
                      if (List.exists (fun v2 -> List.exists (fun v1 -> Var.equal v1 v2) ss ) ts)
                        || (Var.mem s1 nulls && Var.mem t1 nulls)
                      then
                        List.fold_left (fun r f -> begin match f with
                          | CF.Base fb
                          | CF.Exists (fb, _) -> let _, _,_, diseqs, _ = CP.type_decomp fb.Csymheap.base_pure in
                            if List.exists (fun pr1 -> Var.equal_pair_vars (s1,t1) pr1 ) diseqs then
                              r
                            else r@[(vn, f)]
                          | _ -> r@[(vn, f)]
                        end
                        ) [] (CF.list_of_disjuncts (CF.subst sst pdecl.pred_formula))
                      else base_case_unfold_acycli_pure vn pdecl sst dis_prs
                | _ -> []
            in
            if fs != [] then fs
            else aux rest
        with Not_found -> aux rest
      end
    | [] -> []
  in
  try
    aux vns0
  with _ -> []

let search_pred_base_linear_unfold cpreds vns0 eqs nulls=
 let pr1 = PeN.string_of in
  let pr2 = Var.string_of_list in
  let pr3 = pr_list Var.string_of_pair in
  let pr_out = pr_list (pr_pair pr1 CF.string_of) in
  Debug.no_3 "Cpred.search_pred_base_linear_unfold" (pr_list pr1) pr3 pr2 pr_out
      (fun _ _ _ -> search_pred_base_linear_unfold_x cpreds vns0 eqs nulls)
     vns0 eqs nulls


let search_unfold_emp_branch cpreds vns0=
  let unfold_one_emp_brs vn=
    let pdecl = List.find (fun pd -> Ustr.str_eq vn.PeN.hpred_name pd.pred_name) cpreds in
    let emp_brs = List.filter (fun f ->
        let ptos, _ = CF.star_decompose f in
        ptos == []
    ) (CF.list_of_disjuncts  pdecl.pred_formula) in
    if emp_brs == [] then false, []
    else
      let sst = List.combine pdecl.pred_vars vn.PeN.hpred_arguments in
      true, (List.map (fun f -> (vn, CF.subst sst f)) emp_brs)
  in
  let rec fold_left_fast_ret (is_emp, r) vns=
    match vns with
      | vn::rest -> let is_emp, unfold_brs = unfold_one_emp_brs vn in
        if not is_emp then false, r
        else fold_left_fast_ret (is_emp, r@[unfold_brs]) rest
      | [] -> is_emp, r
  in
  fold_left_fast_ret (true, []) vns0

let is_progressing pred=
  let is_progress f=
    let vns, ptos = CF.star_decompose f in
    ptos != [] || List.exists (fun vn -> vn.PeN.hpred_unfold_step > 0) vns
  in
  let fs = CF.list_of_disjuncts pred.pred_formula in
  List.exists is_progress fs
