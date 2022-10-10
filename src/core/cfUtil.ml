open Globals
open Gen
open VarGen

module CF = Cformula
module CSH = Csymheap
module CH = Cheap
module CPred = Cpred
module CPeN = CpredNode
module CPoN = CptoNode

module CP = Cpure

let unfold ?bfs:(is_bfs=false) f=
  []


let h_is_pure pdefs pure_preds h0=
  let rec aux h= match h with
    | CH.Star (h1, h2, _) -> (aux h1) && (aux h2)
    | CH.HTrue -> true
    | CH.PredNode vn -> begin
        if Gen.BList.mem_eq Ustr.str_eq vn.CpredNode.hpred_name pure_preds
        then true else
          (* look up the predicate definiion *)
          try
            let pdef = List.find (fun def ->
                Ustr.str_eq def.Cpred.pred_name vn.CpredNode.hpred_name
            ) pdefs in
            pdef.Cpred.pred_is_pure
          with Not_found -> false
      end
    | _ -> false
  in aux h0

let is_pure_x pdefs pure_preds f0=
  let rec aux f= match f with
      | CF.Base fb -> h_is_pure pdefs pure_preds fb.CSH.base_heap
      | CF.Exists (fb, qvars) -> h_is_pure pdefs pure_preds fb.CSH.base_heap
      | CF.Or (f1, f2, pos) -> (aux f1) && (aux f2)
  in aux f0

let is_pure pdefs pure_preds f0=
  let pr1 = pr_list Cpred.string_of in
  let pr2 = pr_list pr_id in
  Debug.no_3 "is_pure" pr1 pr2 CF.string_of string_of_bool
      (fun _ _ _ -> is_pure_x pdefs pure_preds f0)
      pdefs pure_preds f0

let is_pred_deci pdecls f0=
  let rec aux f= match f with
    | CF.Base fb
    | CF.Exists (fb, _) -> let views, _ = CH.star_decompose fb.CSH.base_heap in
      List.for_all (fun v -> begin
        try
          let decl = List.find (fun d -> Ustr.str_eq d.Cpred.pred_name v.CPeN.hpred_name) pdecls in
          decl.Cpred.pred_is_sat_deci
        with Not_found -> false
      end
      ) views
    | CF.Or (f1, f2, _) -> (aux f1) && (aux f2)
  in aux f0

(*
(* local function *)
*)
let get_call_view_name f =
  let cviews, _ = CF.star_decompose f in
  Gen.BList.remove_dups_eq Ustr.str_eq (List.map (fun v -> v.CpredNode.hpred_name) cviews)

let rec get_closure_preds pdecls fs cur_set=
  match fs with
    | f::tl ->
          let new_set_names = get_call_view_name f in
          let diff = Gen.BList.difference_eq Ustr.str_eq new_set_names
            (List.map (fun d -> d.Cpred.pred_name) cur_set) in
          (* lookup all defns of diff *)
          let preds_diff,fs_diff = List.fold_left (fun (acc1,acc2) vn ->
              let decl = List.find (fun d -> Ustr.str_eq vn d.Cpred.pred_name) pdecls in
              acc1@[decl], acc2@[decl.Cpred.pred_formula]
          ) ([],[]) diff in
          get_closure_preds pdecls (tl@fs_diff) (cur_set@preds_diff)
    | [] -> cur_set


let get_rev_tars vn args rev_pairs rec_fs =
  let tars = List.fold_left (fun r (_,qvars, vns, ptos, p) ->
      let self_rec_vns, sub_vns = List.partition (fun v -> Ustr.str_eq v.CPeN.hpred_name vn) vns in
      (* pair formal args with actual *)
      let self_rec_pairs = List.fold_left (fun r vn -> r@(List.combine vn.CPeN.hpred_arguments args)) [] self_rec_vns in
      let rev_src_tars = List.filter (fun (src, tar) -> begin
        try
          let poss_pairs = List.fold_left (fun r1 pto ->
              if Var.mem tar pto.CPoN.hpto_arguments then
                let (_, src1) = List.find (fun (v, _) -> Var.equal v src) self_rec_pairs in
                if Var.equal src1 src then r1@[(src, tar)]
                else r1
              else r1
          ) [] ptos in
          poss_pairs!=[]
        with Not_found -> false
      end
      ) rev_pairs in
      let tars = Var.remove_dups (List.map snd rev_src_tars) in
      r@tars
    ) ([]) rec_fs in
  Var.remove_dups tars


let check_pred_precise pdecls vn args cf=
  let rec check_connected qvars next_ptrs rest_ptos pairs next_views done_ptrs res not_in=
    match next_ptrs with
      | v::rest -> begin
          let ls = List.filter (fun (v1, _) -> Var.equal v v1 ) pairs in
          match ls with
            | [(_,v2)] -> check_connected qvars rest rest_ptos pairs next_views (done_ptrs@[v]) (res@[v2]) not_in
            | [] -> begin
                let ptos, next_ptos = List.partition (fun pto ->
                    Var.equal v pto.CPoN.hpto_node
                ) rest_ptos in
                match ptos with
                  | [pto] ->
                        let new_next_ptrs = Var.diff pto.CPoN.hpto_arguments (args@done_ptrs) in
                        check_connected qvars (Var.remove_dups (rest@new_next_ptrs)) next_ptos pairs next_views (done_ptrs@[v]) res not_in
                  | _ -> begin
                      (* check connected view *)
                      let ls_pairs, rest_next_views = List.partition (fun (v1, _) -> Var.equal v v1 ) next_views in
                      match ls_pairs with
                        | [(_, v2)] ->
                              let new_next = if Var.mem v2 qvars then [v2] else [] in
                              check_connected qvars (Var.remove_dups (rest@new_next)) next_ptos pairs rest_next_views (done_ptrs@[v]) res not_in
                        | _ -> check_connected qvars rest next_ptos pairs rest_next_views (done_ptrs@[v]) res (not_in@[v])
                    end
              end
            | _ -> false, res, not_in
        end
      | [] -> if rest_ptos ==[] then true, res, not_in else
          false, res, not_in
  in
  let lookup_src_tar_sub_views vn=
    try
      let pdecl = List.find (fun p -> Ustr.str_eq vn.CPeN.hpred_name p.Cpred.pred_name) pdecls in
    match pdecl.Cpred.pred_composition_vars with
      | Some ((src_tars, _, _, _, _, _), _) ->
            if src_tars == [] then [] else
              let sst = List.combine pdecl.Cpred.pred_vars vn.CPeN.hpred_arguments in
              List.map (fun (v1, v2) -> (Var.subst sst v1, Var.subst sst v2) ) src_tars
      | None -> []
    with Not_found -> []
  in
  let rec lookup_target eqs a=
    match eqs with
      | (v1, v2)::rest ->
            if Var.equal v1 a then [(a, v2)]
            else if Var.equal v2 a then [(v1, a)]
            else lookup_target rest a
      | [] -> []
  in
  let extract_base (_, _,_, ptos, p)=
    let eqNull, _, eqs, _, _ = CP.type_decomp p in
    let src_tars, neqNulls = List.fold_left (fun (r1, r2) pto ->
        let srcs0 = Var.get_eq_closure eqs [pto.CPoN.hpto_node] in
        let srcs1 =  Var.intersect srcs0 args in
        if srcs1 == [] then (r1,r2) else
          let targs = Var.intersect pto.CPoN.hpto_arguments args in
          let pairs = List.fold_left (fun r1 src ->
              r1@(List.map (fun t -> (src, t)) targs)
          ) [] srcs1 in
          r1@pairs, r2@srcs1
    ) ([], []) ptos in
    ([Var.get_eq_closure eqs eqNull], eqs, src_tars, neqNulls)
  in
  (**********************************)
  (* TODO: find a decidable fragment with arith properties *)
  (* if List.exists (fun v -> not (is_ptr_arith v.Var.t)) args then None *)
  (* else *)
    let fs = List.map (fun f ->
        let qvars, vns, ptos, p = CF.decompose f in
        (f, qvars, vns, ptos, p)
    ) (CF.list_of_disjuncts cf) in
    let two_ptos = List.exists (fun (_,_,_, ptos, _) -> List.length ptos > 1) fs in
    (* base -rec cases *)
    let base_fs, rec_fs = List.partition (fun (_,_,vns, _, _) -> vns==[]) fs in
    if List.length rec_fs != 1 then
      [], None, [], false, false, []
    else
    (* eqNULL -> src with target is null *)
    let eqNulls, base_eqs, distinct_src_tars, src_neqNulls = match base_fs with
      | bf0::rest ->
            List.fold_left (fun (a1,a2,a3, a4) bf  ->
                let eqNulls, eqs, src_tars, neqNulls =  extract_base bf in
                Gen.BList.intersect_eq (fun ls1 ls2 -> Var.diff ls1 ls2 == []) eqNulls a1 , a2@eqs, a3@src_tars, Var.intersect a4 neqNulls
            ) (extract_base bf0) rest
      | [] -> ([],[],[], [])
    in
    let () = Debug.ninfo_hprint (add_str "base_eqs" (pr_list Var.string_of_pair)) base_eqs no_pos in
    let () = Debug.ninfo_hprint (add_str "distinct_src_tars" (pr_list Var.string_of_pair)) distinct_src_tars no_pos in
    (* eq -> src:target*)
    let srcs_null = match eqNulls with
      | [] -> []
      | ls::rest -> List.fold_left (fun r ls1 -> r@ls1) ls rest in
    let srcs_null1 = Var.remove_dups (Var.intersect srcs_null args) in
    let () = Debug.ninfo_hprint (add_str "srcs_null1" Var.string_of_list) srcs_null1 no_pos in
    (* src - target *)
    let is_connected, srcs, local_precise_srcs (*precise*), expect_srcs, nonlocal_precise_srcs, nonlocal_ext_srcs, cond_acyclic, non_compos, acyc_flags, local_ext_srcs, dis_srcs = List.fold_left (fun (b,r1, r_lp_srcs, r2, r4, r4b, r3, bnon_com, r5, r_le_srcs, r7) (_,qvars, vns, ptos, p) -> begin
      let eqNulls, _, _, neqs, p = CP.type_decomp p in
      let self_rec_vns, sub_vns = List.partition (fun v -> Ustr.str_eq v.CPeN.hpred_name vn) vns in
      (* pair formal args with actual *)
      let self_rec_pairs = List.fold_left (fun r vn -> r@(List.combine vn.CPeN.hpred_arguments args)) [] self_rec_vns in
      let srcs, next_ptrs, next_ptos = List.fold_left (fun (r1,r2, r3) pto ->
          if Var.mem pto.CPoN.hpto_node args then
            (r1@[pto.CPoN.hpto_node], r2@(Var.diff pto.CPoN.hpto_arguments eqNulls), r3)
          else (r1, r2, r3@[pto])
      ) ([], [], []) ptos in
      let srcs1 = Var.remove_dups srcs in
      let local_srcs0, next_ptrs = List.partition (fun v -> Var.mem v args) next_ptrs in
      let dis_spatial_srcs = List.filter (fun sv -> List.exists (fun (sv1, sv2) -> Var.equal sv sv1 || Var.equal sv sv2) neqs) local_srcs0 in
      let n_bnon_com = dis_spatial_srcs != [] in
      let ps = (Cpure.split_conjunctions p) in
      let local_precise_srcs, acyc_ls, local_ext_srcs, dis_srcs = List.fold_left (fun (r1,r2,r3, r4) v -> begin
        try
          let p= List.find (fun p -> Var.mem v (CP.fv p)) ps in
          let is_ext, is_dis, is_local = Cpure.is_local_constraint p in
          let n_r4 = if is_dis then r4@[v] else r4 in
          if is_local then
            if is_ext then
              (r1, r2@[is_dis], r3@[v], n_r4)
            else (r1@[v], r2@[is_dis], r3, n_r4)
          else (r1, r2, r3, n_r4)
        with Not_found -> (r1@[v], r2@[false], r3, r4)
      end
      ) ([],[],[], []) local_srcs0 in
      let nonlocal_precise_srcs, nonlocal_ext_srcs, non_local_dis_srcs = List.fold_left (fun (r1, r1b, r2) v -> begin
        let ps1 =  List.filter (fun p -> Var.mem v (CP.fv p)) ps in
        if ps1 == [] then (r1, r1b, r2) else
          let is_ext, is_local = List.fold_left (fun (r1, r2) p ->
              let is_ext, is_dis, is_local = Cpure.is_local_constraint p in
              r1&& is_ext, r2 &&is_local && is_dis
          ) (true, true) ps1 in
          if is_local then
            if is_ext then (r1, r1b@[v], r2@[v])
            else (r1@[v], r1b, r2@[v])
          else (r1, r1b, r2)
      end
      ) ([],[],[]) (Var.diff args (srcs1@local_precise_srcs@local_ext_srcs)) in
      let () = Debug.ninfo_hprint (add_str "srcs1" Var.string_of_list) srcs1 no_pos in
      let () = Debug.ninfo_hprint (add_str "dis_srcs@non_local_dis_srcs" Var.string_of_list) (dis_srcs@non_local_dis_srcs) no_pos in
      let () = Debug.ninfo_hprint (add_str "local_precise_srcs" Var.string_of_list) local_precise_srcs no_pos in
      let () = Debug.ninfo_hprint (add_str "local_ext_srcs" Var.string_of_list) local_ext_srcs no_pos in
      let () = Debug.ninfo_hprint (add_str "acyc_local list" (pr_list string_of_bool)) acyc_ls no_pos in
      let () = Debug.ninfo_hprint (add_str "nonlocal_precise_srcs" Var.string_of_list) nonlocal_precise_srcs no_pos in
      let () = Debug.ninfo_hprint (add_str "next_ptrs" Var.string_of_list) next_ptrs no_pos in
      let next_views = List.fold_left (fun r vn ->
          let src_tars = lookup_src_tar_sub_views vn in
          r@src_tars
      ) [] sub_vns in
      let () = Debug.ninfo_hprint (add_str "next_views" (pr_list Var.string_of_pair)) next_views no_pos in
      (* support connected ptos *)
      (* all quantified parameter are connected? *)
      let q_next_ptrs = Var.diff next_ptrs args in
      let b1, expect_allocated_args, not_in_next_ptrs = check_connected qvars q_next_ptrs next_ptos self_rec_pairs next_views (srcs1@eqNulls) [] [] in
      let () = Debug.ninfo_hprint (add_str "not_in_next_ptrs" Var.string_of_list) not_in_next_ptrs no_pos in
      (*TEMP: nested ==> non-composition *)
      let is_nested = List.exists (fun vnode -> not (Ustr.str_eq vn vnode.CPeN.hpred_name)) vns in
      (* check whether not_in_next_ptrs is a subset of next_ptrs *)
      let b2 = b1 && (not_in_next_ptrs == [] ||
          ((Var.diff not_in_next_ptrs q_next_ptrs ==[]) && (List.length not_in_next_ptrs < List.length q_next_ptrs))) in
      b && b2, r1@srcs1, r_lp_srcs@local_precise_srcs, r2@expect_allocated_args, r4@nonlocal_precise_srcs, r4b@nonlocal_ext_srcs,r3@[neqs],
      (bnon_com||n_bnon_com||is_nested), (r5@acyc_ls), (r_le_srcs@local_ext_srcs), r7@dis_srcs@dis_spatial_srcs@non_local_dis_srcs
    end
    ) (true, [], [], [], [], [], [], false, [], [], []) rec_fs in
    let () = Debug.ninfo_hprint (add_str "cond_acyclic" (pr_list (pr_list Var.string_of_pair))) cond_acyclic no_pos in
    let srcs_null2 = Var.intersect srcs_null1 srcs in
    let src_neqNulls1 = Var.intersect (Var.remove_dups src_neqNulls) srcs in
    let () = Debug.ninfo_hprint (add_str "srcs_null2" Var.string_of_list) srcs_null2 no_pos in
    let () = Debug.ninfo_hprint (add_str "src_neqNulls1" Var.string_of_list) src_neqNulls1 no_pos in
    let roots = srcs_null2@src_neqNulls1 in
    (*TODO: check src!=tar in all neqs*)
    let is_acyclic = List.exists (fun ls -> ls != []) cond_acyclic in
    if not is_connected || srcs == [] || (Var.diff expect_srcs srcs != []) then
      if roots ==[]  then roots, None, get_rev_tars vn args (base_eqs@distinct_src_tars) rec_fs, is_acyclic, false, []
      else
        roots, None, [], true, false, []
    else
      let all_eqs = base_eqs@distinct_src_tars in
      (* compose targets *)
      let src_tars0 = List.fold_left (fun r a ->
          begin
            let pairs = lookup_target (all_eqs) a in
            r@pairs
          end
      ) [] srcs in
      let dis_prs = List.fold_left (fun r a ->
          begin
            let pairs = lookup_target (all_eqs) a in
            r@pairs
          end
      ) [] dis_srcs in
      let src_tars = Gen.BList.remove_dups_eq Var.equal_pair_vars src_tars0 in
      let local_precise_src_tars = List.fold_left (fun r a ->
          begin
            let pairs = lookup_target (all_eqs) a in
            r@pairs
          end
      ) [] local_precise_srcs in
      let local_ext_src_tars = List.fold_left (fun r a ->
          begin
            let pairs = lookup_target (all_eqs) a in
            r@pairs
          end
      ) [] local_ext_srcs in
      let all_eqs_used = local_ext_src_tars@local_precise_src_tars in
      let all_eqs_left = List.filter (fun pr1 ->
          List.for_all (fun pr2 -> not (Var.equal_pair_vars pr1 pr2)) all_eqs_used
      ) all_eqs in
      let nonlocal_precise_src_tars = List.fold_left (fun r a ->
          begin
            let pairs = lookup_target (all_eqs_left) a in
            r@pairs
          end
      ) [] nonlocal_precise_srcs in
      let nonlocal_ext_src_tars = List.fold_left (fun r a ->
          begin
            let pairs = lookup_target (all_eqs_left) a in
            r@pairs
          end
      ) [] nonlocal_ext_srcs in
      (* neq src_atr in recur *)
      let () = Debug.ninfo_hprint (add_str "src_tars" (pr_list (pr_pair Var.string_of Var.string_of))) src_tars no_pos in
      let () = Debug.ninfo_hprint (add_str "local_precise_src_tars" (pr_list (pr_pair Var.string_of Var.string_of))) local_precise_src_tars no_pos in
      if not two_ptos && (roots != [] || src_tars != []) && (List.for_all (fun (v1, v2) -> List.for_all (fun (v3, v4) -> not (Var.mem v1 [v3;v4] || Var.mem v2 [v3;v4] ) ) src_tars)  local_precise_src_tars) then
        let () = Debug.ninfo_hprint (add_str "local_ext_src_tars" (pr_list (pr_pair Var.string_of Var.string_of))) local_ext_src_tars no_pos in
        let () = Debug.ninfo_hprint (add_str "nonlocal_precise_src_tars" (pr_list (pr_pair Var.string_of Var.string_of))) nonlocal_precise_src_tars no_pos in
        let () = Debug.ninfo_hprint (add_str "non_compos" (string_of_bool)) non_compos no_pos in
        let () = Debug.ninfo_hprint (add_str "roots" (pr_list (Var.string_of))) roots no_pos in
        roots, Some ((src_tars, local_precise_src_tars, local_ext_src_tars , nonlocal_precise_src_tars, nonlocal_ext_src_tars,
        Var.diff args (srcs_null2@(List.fold_left (fun r (sv1, sv2) -> r@[sv1;sv2]) [] (src_tars@local_precise_src_tars@local_ext_src_tars@nonlocal_precise_src_tars@nonlocal_ext_src_tars)))), dis_prs),
  [], is_acyclic, not non_compos, acyc_flags
      else
        roots, None, get_rev_tars vn args (base_eqs@distinct_src_tars) rec_fs, is_acyclic, false, []

let extend_pred_defn_x vn args roots precise_args cf=
  let is_extensible () = match precise_args with
    | Some ((src_tars, _, _, _, _,  _), _) -> begin
        match src_tars with
          | [] -> false
          | _ -> true
      end
    | None -> false
  in
  let is_precise recp=
    let _, neqnulls, _, diseqs, _ = CP.type_decomp recp in
    if diseqs == [] then false else
      let  pairs = match  precise_args with
        | Some ((src_tars, _, _, _, _ ,_), _) ->  src_tars
        | None ->  []
      in
      let neqnulls1 = Var.intersect neqnulls args in
      if Var.diff neqnulls1 roots != [] then false else
        List.for_all (fun (v1, v2) ->
            List.exists (fun (v3, v4) ->
                ((Var.equal v1 v3) && (Var.equal v2 v4)) ||
                    ((Var.equal v1 v4) && (Var.equal v2 v3))
            ) diseqs
        ) pairs
  in
  if not (is_extensible ()) then []
  else
    let fs = List.map (fun f ->
        let qvars, vns, ptos, p = CF.decompose f in
        (f, qvars, vns, ptos, p)
    ) (CF.list_of_disjuncts cf) in
    (* base -rec cases *)
    let base_fs, rec_fs = List.partition (fun (_,_,vns, _, _) -> vns==[]) fs in
    match base_fs, rec_fs with
      | [(bf, bqvars, bvns, bptos, bp)], [(recf, recqvars, recvns, recptos, rp)] -> begin
          if CF.isHTrueHeap bf && is_precise rp then
            (* first  case: empty *)
            let emp_bf = CF.mkExists bqvars CH.HEmp bp no_pos in
            (* second case: non-empty *)
            match recf with
              | CF.Base fb
              | CF.Exists (fb, _) ->
                    let recqvars1 = Var.intersect recqvars (CH.fv fb.CSH.base_heap) in
                    (* fresh quantifiers *)
                    let recqvars2 = Var.fresh_vars recqvars1 in
                    let sst1 = List.combine recqvars1 recqvars2 in
                    let h = CH.h_subst sst1 fb.CSH.base_heap in
                    let bqvars2 = Var.fresh_vars bqvars in
                    let sst2 = List.combine bqvars bqvars2 in
                    let bp1 = CP.subst_var sst2 bp in
                    let nonemp_bf = CF.mkExists (bqvars2@recqvars2) h bp1 no_pos in
                    [emp_bf; nonemp_bf; recf]
              | CF.Or _ -> []
          else []
        end
      | _ -> []

let extend_pred_defn vn args roots precise_args cf=
  let pr1 (( a, b,c, d,_,_), _) = (pr_list Var.string_of_pair) (a@b@c@d) in
  let pr2 = CF.string_of in
  Debug.no_4 "extend_pred_defn" pr_id Var.string_of_list
      (pr_option pr1) pr2 (pr_list_ln pr2)
      (fun _ _ _ _ -> extend_pred_defn_x vn args roots precise_args cf)
      vn args precise_args cf

let unfold_base_pair_x pdecls buse_buds f=
  let vns, _ = CF.star_decompose f in
  let f1 = List.fold_left (fun r vn -> CF.subtract_pred r vn) f vns in
  let _, fs = List.fold_left (fun (b,r) vn -> begin
    try
      if b then
        (* stop when one view is false *)
        b,r
      else
        let pdecl = List.find (fun p -> Ustr.str_eq vn.CPeN.hpred_name p.Cpred.pred_name) pdecls in
        let bases,  buds = pdecl.Cpred.pred_base in
        let sst = List.combine pdecl.Cpred.pred_vars vn.CPeN.hpred_arguments in
        match bases with
          | [] -> b,r
          | [f] -> if CF.isFalse f then true, [f] else
              if not buse_buds then
              let f2 = CF.subst sst f in
              b, List.map (fun f1 -> CF.mkStarAnd f2 f1) r
              else
                let nr = List.fold_left (fun a f ->
                a@(List.map (fun f1 -> CF.mkStarAnd f f1) r)
                ) [] (List.map (CF.subst sst) ([f]@buds))
                in
                b, nr
          | fs ->
                let fs1 = if not buse_buds then fs
                else fs@buds in
                let nr = List.fold_left (fun a f ->
                a@(List.map (fun f1 -> CF.mkStarAnd f f1) r)
            ) [] (List.map (CF.subst sst) (fs1))
            in
            b, nr
    with Not_found -> b,r
  end
  ) (false, [f1]) vns in
  fs

let unfold_base_pair pdecls buse_buds f =
  let pr1 = CF.string_of in
  Debug.no_2 "unfold_base_pair" pr1 string_of_bool (pr_list_ln pr1)
      (fun _ _ -> unfold_base_pair_x pdecls buse_buds f) f buse_buds

let unfold_pred pdecls vn=
  let pdecl = List.find (fun pd -> Ustr.str_eq vn.CPeN.hpred_name pd.Cpred.pred_name) pdecls in
  let args = Var.fresh_vars pdecl.Cpred.pred_vars in
  let sst0 = List.combine pdecl.Cpred.pred_vars args in
  let defn = match pdecl.Cpred.pred_unfolded_formula with
    | [] ->  pdecl.Cpred.pred_formula
    | _ -> CF.to_disjunct_form pdecl.Cpred.pred_unfolded_formula
  in
  let pred_defn = CF.subst sst0 defn in
  let sst = List.combine args vn.CPeN.hpred_arguments in
  CF.subst sst pred_defn

let compute_br_inv_x pdecls vn args cf null_svs precise_vars=
  match precise_vars with
    | Some ((src_tar_ls, _, _, _,  _, _), _) -> begin
        let fs = List.map (fun f ->
            let qvars, vns, ptos, p = CF.decompose f in
            (f, qvars, vns, ptos, p)
        ) (CF.list_of_disjuncts cf) in
        (* base -rec cases *)
        let base_fs, rec_fs = List.partition (fun (_,_,vns, _, _) -> vns==[]) fs in
        match base_fs, rec_fs with
          | [(bf, bqvars, bvns, bptos, bp)], [(recf, recqvars, recvns, recptos, rp)] -> begin
              if null_svs != [] then
                []
              else if src_tar_ls !=[] then
                if not (CP.isTrue bp) && not (CP.isTrue rp) then
                  [(bp, bf); (rp, recf)]
                else []
              else []
            end
          | _ -> []
      end
    | None -> []

let compute_br_inv pdecls vn args cf null_svs precise_vars=
  let pr1 = pr_option (pr_pair (pr_hexa (pr_list Var.string_of_pair) (pr_list Var.string_of_pair) (pr_list Var.string_of_pair) (pr_list Var.string_of_pair) (pr_list Var.string_of_pair) Var.string_of_list) (pr_list Var.string_of_pair) ) in
  let pr2 = CF.string_of in
  let pr_out = pr_list_ln (pr_pair CP.string_of pr2) in
  Debug.no_4 "compute_br_inv" pr_id Var.string_of_list pr2
      pr1 pr_out
      (fun _ _ _ _ -> compute_br_inv_x pdecls vn args cf null_svs precise_vars)
      vn args cf precise_vars

let sequentialize_and_unfold_flat_views_x pdecls cf=
  let unfold_one f (vn, br)=
    let br1 = (CF.fresh_quantifiers br) in
    let nf1 = CF.mkStarAnd br1 f in
    nf1
  in
  let aux_unfold_nonrec f=
    let vns, _ = CF.star_decompose f in
    let non_rec_vns, non_rec_lbls = List.fold_left (fun (r1,r) vn -> begin
      try
        let pdecl = List.find (fun pd -> Ustr.str_eq vn.CPeN.hpred_name pd.Cpred.pred_name) pdecls in
        if pdecl.Cpred.pred_rec == NOREC then
          let args = Var.fresh_vars pdecl.Cpred.pred_vars in
          let sst0 = List.combine pdecl.Cpred.pred_vars args in
          let pred_defn = CF.subst sst0 pdecl.Cpred.pred_formula in
          let sst = List.combine args vn.CPeN.hpred_arguments in
          let cf = CF.subst sst pred_defn in
          (r1@[vn], r@[(vn, cf)])
        else (r1,r)
      with Not_found -> (r1,r)
    end
    ) ([],[]) vns in
    if non_rec_lbls == [] then [f] else
      (*subtract nonrec views*)
      let f1 = List.fold_left (fun r vn -> CF.subtract_pred r vn) f non_rec_vns in
      let fs = List.fold_left (fun r_out (vn, br) ->
          List.fold_left (fun r f -> let f1 =  unfold_one f (vn, br) in
          let () = Debug.ninfo_hprint (add_str "f1" CF.string_of) f1 no_pos in
          let is_unsat, f2 = CF.remove_redundant f1 in
          let () = Debug.ninfo_hprint (add_str "f2" CF.string_of) f2 no_pos in
          if is_unsat then r else
            let f3 = CF.remove_dups f2 in
            r@[f3]
          ) [] r_out
      ) [f1] non_rec_lbls in
      fs
      (* List.fold_left (fun r f2 -> *)
          (* let is_unsat, f3 = CF.remove_redundant f2 in *)
      (*     if is_unsat then r else r@[f2] *)
      (* ) [] fs *)
  in
  if List.length pdecls == 1 || !VarGen.sat_early_detect_non_progress then CF.sequentialize_views cf
  else
    let fs = CF.list_of_disjuncts cf in
    let fs1 = List.fold_left (fun r f -> r@(aux_unfold_nonrec f)
    ) [] fs in
    CF.sequentialize_views (CF.to_disjunct_form fs1)

let sequentialize_and_unfold_flat_views pdecls cf=
  let pr1 = pr_list_ln Cpred.string_of in
  let pr2 = CF.string_of in
  Debug.no_2 "sequentialize_and_unfold_flat_views"
      pr1 pr2 pr2 (fun _ _ -> sequentialize_and_unfold_flat_views_x pdecls cf) pdecls cf

let set_progressing_step cf=
  let aux_h h=
    (* let vns, ptos = CH.star_decompose h in *)
    (* if ptos == [] then *)
      CH.clear_view_unfold_step h
    (* else h *)
  in
  let rec aux_count f=
    match f with
      | CF.Base fb -> let _, ptos = CH.star_decompose fb.CSH.base_heap in
        if ptos == [] then 0 else 1
      | CF.Exists (fb, _) ->
             let _, ptos = CH.star_decompose fb.CSH.base_heap in
        if ptos == [] then 0 else 1
      | CF.Or (f1, f2, pos) -> let c1 = aux_count f1 in
        if c1 == 0 then aux_count f2 else c1
  in
  let rec aux f=
    match f with
      | CF.Base fb ->
            CF.Base {fb with CSH.base_heap = aux_h fb.CSH.base_heap}
      | CF.Exists (fb, qvars) ->
            CF.Exists ({fb with CSH.base_heap = aux_h fb.CSH.base_heap}, qvars)
      | CF.Or (f1, f2, pos) -> CF.Or (aux f1, aux f2, pos)
  in
  let pto_num =  aux_count cf in
  if pto_num == 0 then
    aux cf
  else cf


let skolem_rhs_arith_x qvars0 f=
  let do_split qvars p=
    let ps = CP.split_conjunctions p in
    let ps1, ps2 = List.partition (fun p ->
        match p with
          | CP.BForm (Term.Eq ((Exp.Var (v1, _)), e0, _ )) -> begin
              match e0 with
                | (Exp.Add (e1,e2,_))
                | (Exp.Subtract (e1,e2,_)) -> begin
                    match e1, e2 with
                      | Exp.Var (v2,_), Exp.IConst _
                      | Exp.IConst _, Exp.Var (v2,_) ->
                            not (Var.mem v1 qvars) && (Var.mem v2 qvars)
                      | _ -> false
                  end
                | _ -> false
            end
          | _ -> false
    ) ps in
    if ps1 == [] then None
    else Some (CP.join_conjunctions ps2 no_pos, CP.join_conjunctions ps1 no_pos)
  in
  match f with
    | CF.Base fb -> begin
          let p_vs = CP.fv fb.CSH.base_pure in
          if List.for_all (fun v -> not (Var.mem v qvars0)) p_vs then
            None
          else
            let r = do_split qvars0 fb.CSH.base_pure in
            match r with
              | Some (p1, p2) -> Some (CF.Base {fb with CSH.base_pure = p1}, p2)
              | None -> None
      end
    | CF.Exists (fb, qvars) -> begin
        let p_vs = CP.fv fb.CSH.base_pure in
        let qvars1 = qvars0@qvars in
        if List.for_all (fun v -> not (Var.mem v qvars1)) p_vs then
            None
          else
            let r = do_split qvars1 fb.CSH.base_pure in
            match r with
              | Some (p1, p2) ->
                    let qvars3 = CP.fv p2 in
                    Some (CF.Exists({fb with CSH.base_pure = p1},
                    List.filter (fun v -> not (Var.mem v qvars3)) qvars), p2)
              | None -> None
      end
    | _ -> None

let skolem_rhs_arith qvars0 f=
  let pr1 = CF.string_of in
  let pr2 = pr_pair pr1 CP.string_of in
  Debug.no_2 "skolem_rhs_arith" Var.string_of_list pr1
      (pr_option pr2)
      (fun _ _ -> skolem_rhs_arith_x qvars0 f) qvars0 f
