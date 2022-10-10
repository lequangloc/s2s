open Globals
open Gen
open VarGen

open EntType

module CF = Cformula
module PeN = CpredNode
module PoN = CptoNode

module CH = Cheap

module CP = Cpure

module SLND = SlNode.SL_NODE_DATA
module SLN = SlNode

module SUBT = EntType.SUBT
module SUBT_elm = EntType.SL_SUBTERM_ELT

let search_match_comp_view_x cpreds (subterm_map: SUBT.t list) cview cqvars
      bud_views bqvars=
  let rec match_univ_args sst=
    match sst with
      | (ba,ca)::rest ->
            if Var.mem ba bqvars || Var.mem ca cqvars then
              match_univ_args rest
            else (* both are univ *)
              if Var.equal ba ca then true
            else false (* match_univ_args_num rest *)
      | [] -> false
  in
  let bview = List.find (fun bv -> begin
      let () = Debug.ninfo_hprint (add_str  "link_back (bv.PN.hpred_name)"
          pr_id) bv.PeN.hpred_name no_pos in
      if not (Ustr.str_eq cview.PeN.hpred_name bv.PeN.hpred_name) then
        false
      else
        if SUBT_elm.equal bv cview then
          true
        else
          (* look up the pair (cview, bv) in subterm_map *)
          let inter_submap = List.filter (fun ls ->
              SUBT.mem cview ls
          ) subterm_map in
          let is_subterm =  List.exists (fun ls ->
              SUBT.mem bv ls
          ) inter_submap in
          if is_subterm then true
          else
            (* consider cview with qvars *)
            List.exists (fun ls ->
                List.exists (fun v ->
                    if not (Ustr.str_eq bv.PeN.hpred_name v.PeN.hpred_name) then
                      false
                    else
                      match_univ_args
                          (List.combine bv.PeN.hpred_arguments v.PeN.hpred_arguments)
                ) ls
            ) inter_submap
  end
  ) bud_views in
  bview

let search_match_comp_view cpreds (subterm_map: SUBT.t list) cview cqvars
      bud_views bqvars=
  let pr1 = pr_list_ln SUBT.string_of in
  let pr2 = PeN.string_of in
  Debug.no_5 "search_match_comp_view" pr1 pr2 Var.string_of_list
      (pr_list pr2) Var.string_of_list pr2
      (fun _ _ _ _ _ -> search_match_comp_view_x cpreds subterm_map cview cqvars
      bud_views bqvars) subterm_map cview cqvars
      bud_views bqvars

let search_match_comp_views cpdecls (subterm_map: SUBT.t list) comp_views cqvars
      bud_views bqvars=
  let rec fold_left_aux cviews (acc_link, acc_sub, acc_sst) =
    match cviews with
      | cview::rest ->
            let () = Debug.ninfo_hprint (add_str  "link_back (cview.PN.hpred_name)"
                pr_id) cview.PeN.hpred_name no_pos in
            let bview = search_match_comp_view cpdecls subterm_map cview cqvars bud_views bqvars in
            let () = Debug.ninfo_hprint (add_str  "link_back (bview.PN.hpred_name)"
                pr_id) bview.PeN.hpred_name no_pos in
            let is_global_sound = cview.PeN.hpred_unfold_num < bview.PeN.hpred_unfold_num in
            let is_sub = if not is_global_sound then false else
              true
            in
            let sst0 = List.fold_left (fun acc (v1,v2) ->
                if not (Var.equal v1 v2) then acc@[(v1,v2)] else acc
            ) [] (List.combine cview.PeN.hpred_arguments bview.PeN.hpred_arguments) in
            let n_rest = List.map (fun cview -> PeN.subst sst0 cview) rest in
            let n_acc_link = acc_link@[(cview,bview)] in
            let n_acc_sub = acc_sub || is_sub in
            let n_sst = acc_sst@sst0 in
            fold_left_aux n_rest (n_acc_link, n_acc_sub, n_sst)
      | [] -> (acc_link, acc_sub, acc_sst)
  in
  fold_left_aux comp_views ([], false, [])

let search_match_bud_pto_x is_heap_only sst0 comp_ptos comp_qvars ceqs
      bud_ptos bud_qvars beqs=
  let rec eq_quan_vars pr_args res=
    match pr_args with
      | (c_arg, b_arg)::rest -> begin
          let b1 =  Var.mem b_arg bud_qvars in
          let b2 =  Var.mem c_arg comp_qvars in
          match b1, b2 with
            | false, false -> let new_res = if Var.equal b_arg c_arg then
                res
              else (res@[(c_arg, b_arg)])
              in
              eq_quan_vars rest new_res
            | false, true ->
                  eq_quan_vars rest (res@[(c_arg, b_arg)])
            | true, true  ->
                  eq_quan_vars rest (res@[(c_arg, b_arg)])
            | _ -> eq_quan_vars rest res
        end
      | [] -> res
  in
  let rec eq_univ_vars_x pr_args res=
    match pr_args with
      | (c_arg, b_arg)::rest -> begin
          let b1 =  Var.mem b_arg bud_qvars in
          let b2 =  Var.mem c_arg comp_qvars in
          match b1, b2 with
            | false, false -> let new_res = if Var.equal b_arg c_arg then
                res
              else (res@[(c_arg, b_arg)])
              in
              eq_univ_vars_x rest new_res
            | _ -> eq_univ_vars_x rest res
        end
      | [] -> res
  in
  let eq_univ_vars pr_args res=
    let pr2 = pr_list (pr_pair Var.string_of Var.string_of) in
    Debug.no_1 "eq_univ_vars" pr2 pr2
        (fun _ -> eq_univ_vars_x pr_args res) pr_args
  in
  let rec find_exact_match bptos cpto done_bptos=
    match bptos with
      | bpto::rest ->
            if PoN.equal cpto bpto then
              (bpto, done_bptos@rest)
            else find_exact_match rest cpto (done_bptos@[bpto])
      | [] -> raise Not_found
  in
  let rec find_match bptos cvars bdone match_fnc=
    match bptos with
      | bpto::rest ->
            let bvars = [bpto.PoN.hpto_node]@bpto.PoN.hpto_arguments in
            if Var.intersect cvars bvars != [] then
              let sst = match_fnc (List.combine cvars bvars) [] in
              let is_nonconsistent = List.exists (fun (v1, v2) ->
                  List.exists (fun (v3, v4) -> Var.equal v3 v2 && Var.equal v4 v1) sst0
              ) sst in
              if is_nonconsistent then find_match rest cvars (bdone@[bpto]) match_fnc
              else
                bpto, sst, bdone@rest
            else
              find_match rest cvars (bdone@[bpto]) match_fnc
      | [] -> raise Not_found
  in begin
    let bud_match, sst, bud_rest = List.fold_left (fun (r1, r2, r3) cpto -> begin
      let r31 = (List.filter (fun bp ->
              Ustr.str_eq cpto.PoN.hdata_name bp.PoN.hdata_name) r3) in
      try
        let bpto, brest = find_exact_match r3 cpto [] in
        (r1@[bpto], r2, brest)
      with Not_found -> begin
        try
          let cvars = (* List.map (Var.subst sst0) *) ([cpto.PoN.hpto_node]@cpto.PoN.hpto_arguments) in
          let bpto, sst, brest = find_match r31 cvars [] eq_univ_vars in
          (r1@[bpto], r2@sst, brest)
        with Not_found -> begin
          if is_heap_only then raise Not_found else
          let cvars = List.map (Var.subst sst0) ([cpto.PoN.hpto_node]@cpto.PoN.hpto_arguments) in
          let bpto, sst, brest = find_match r31 cvars [] eq_quan_vars in
          (r1@[bpto], r2@sst, brest)
        end
      end
    end
    ) ([],[], bud_ptos) comp_ptos in
    bud_match, sst, bud_rest
  end

let search_match_bud_pto is_heap_only sst0 comp_ptos comp_qvars ceqs
      bud_ptos bud_qvars beqs=
  let pr1 = pr_list (Var.string_of_pair) in
  let pr2 = pr_list PoN.string_of in
  let pr_out = pr_triple pr2 pr1 pr2 in
  Debug.no_7 "search_match_bud_pto" pr1 pr2 Var.string_of_list pr1 pr2 Var.string_of_list pr1 
      pr_out (fun _ _ _ _ _ _ _ -> search_match_bud_pto_x is_heap_only sst0 comp_ptos comp_qvars ceqs
      bud_ptos bud_qvars beqs) sst0 comp_ptos comp_qvars ceqs
      bud_ptos bud_qvars beqs

let is_match_rhs_back_link_x sst rhs_comp rhs_bud lhs_bud_ptos fp=
  (* subst *)
  let rhs_comp1 = SLND.subst sst rhs_comp in
  let comp_qvars, comp_views, comp_ptos, _,_ = SLN.star_decompose rhs_comp1 in
  let comp_pure = SLND.to_pure rhs_comp1 in
  let bud_qvars, bud_views, bud_ptos, _, _ = SLN.star_decompose rhs_bud in
  let bud_pure = SLND.to_pure rhs_bud in
  if (List.length comp_views) != (List.length bud_views) ||
    (List.length comp_ptos) != (List.length bud_ptos) then false
  else
    let b1 = List.for_all (fun cv -> List.exists (fun bv -> PeN.equal cv bv) bud_views) comp_views in
    let b2 =  List.for_all (fun cv -> List.exists (fun bv -> PoN.equal cv bv) bud_ptos) comp_ptos in
    if b1 && b2 && (CP.equal comp_pure bud_pure) then
      true
    else
      let comp_ps = CP.split_conjunctions comp_pure in
      let bud_ps = CP.split_conjunctions bud_pure in
      let _, fp_ptos = CH.star_decompose fp in
      let fp_p = PoN.to_abs_pure_form (lhs_bud_ptos@fp_ptos) in
      let fp_ps = CP.split_conjunctions fp_p in
      if List.for_all (fun bp -> List.exists (fun cp -> CP.equal bp cp) comp_ps ||
          List.exists (fun fp -> CP.equal bp fp) fp_ps
 ) bud_ps then true else
        (* TODO: consider qvars *)
        false

let is_match_rhs_back_link sst rhs_comp rhs_bud lhs_bud_ptos fp=
  let pr1 = pr_list Var.string_of_pair in
  let pr2 = SLND.string_of in
  Debug.no_3 "is_match_rhs_back_link" pr1 pr2 pr2 string_of_bool
      (fun _ _ _ -> is_match_rhs_back_link_x sst rhs_comp rhs_bud lhs_bud_ptos fp)
      sst rhs_comp rhs_bud

let unify_views_same_spatial_x sst rhs_comp rhs_bud=
  let rec aux comp_vns bud_vns res=
    match comp_vns with
      | cvn::rest -> begin
          let match_bvns, rem = List.partition (fun bvn ->
              if Ustr.str_eq cvn.CpredNode.hpred_name bvn.CpredNode.hpred_name then
                let pr_args = List.combine cvn.CpredNode.hpred_arguments bvn.CpredNode.hpred_arguments in
                List.for_all (fun (v1, v2) ->
                    not (Var.is_node v1) ||
                        (Var.equal v1 v2)
                ) pr_args
              else false
          ) bud_vns in
          match match_bvns with
            | [] -> aux rest bud_vns res
            | bvn::rem2 ->
                  let pr_args = List.combine cvn.CpredNode.hpred_arguments bvn.CpredNode.hpred_arguments in
                  let nsst = List.filter (fun (v1, _) -> not (Var.is_node v1)) pr_args in
                  aux rest (rem@rem2) (res@nsst)
        end
      | [] -> res
  in
  let vs = SLND.fv rhs_comp in
  if List.for_all (Var.is_node) vs then [] else
    let rhs_comp1 = SLND.subst sst rhs_comp in
    let _, comp_vns, _,_,_ = SLN.star_decompose rhs_comp1 in
    let bqvars, bud_vns, _, _,_ = SLN.star_decompose rhs_bud in
    let nsst0 = aux comp_vns bud_vns [] in
    let nsst = List.filter (fun (_,v) -> not (Var.mem v bqvars)) nsst0 in
    let fr_vs = List.map fst nsst in
    let fr_vs1 = Var.remove_dups fr_vs in
    if List.length fr_vs1 < List.length fr_vs then
      []
    else nsst

let unify_views_same_spatial sst rhs_comp rhs_bud=
  let pr1 = SLND.string_of in
  let pr2 = pr_list (Var.string_of_pair) in
  Debug.no_3 "unify_views_same_spatial" pr2 pr1 pr1 pr2
      (fun _ _ _ -> unify_views_same_spatial_x sst rhs_comp rhs_bud)
      sst rhs_comp rhs_bud
