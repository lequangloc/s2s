open Globals
open Gen.Basic
open VarGen

open Com

module CF = Cformula
module CP = Cpure
module PeN = CpredNode

module T = SlTree
module E = SlEdge
module N = SlNode.SLNODE
module SL_ENTRY = SlNode.SL_NODE_DATA

let check_sat_from_data pdecls is_shape_only is_link_back_heap_only
      is_sat_check eager get_cex root_data bound t_size =
  let root = N.mk (root_parent_ID+1) root_data root_parent_ID
    [] 0 Nopen in
  let t = new T.cyclic pdecls root
    is_shape_only  (not is_shape_only) is_link_back_heap_only is_sat_check get_cex
    (eager && is_sat_check) bound t_size in
  try
    let () = t # build_proof () in
    t # find_satisfiability ()
  with e -> begin
    match e with
      | Invalid_argument s ->
        let () = print_endline_quiet ("S2SAT:" ^ s) in
        Out.UNKNOWN, [],[]
      | Com.EARLY_SAT_DECT_EXC -> (Out.SAT, [],[])
      | _ -> Out.UNKNOWN, [],[]
  end

let build_base_pair_or_sat pdecls is_shape_only is_link_back_heap_only
      is_sat_check eager get_cex f0 bound t_size=
  let () = Debug.ninfo_hprint (add_str  "build_base_pair: f0" CF.string_of)
          f0 no_pos in
  let f = CF.sequentialize_views f0 in
  let root_data = SlNode.mk_data pdecls true f in
  (* let d = new En.sl_entry root_data in *)
  (* let root = new N.node (root_parent_ID+1) d root_parent_ID *)
  (*   [] 0 Nopen in *)
  (* let root = N.mk (root_parent_ID+1) root_data root_parent_ID *)
  (*   [] 0 Nopen in *)
  (* let heap_only = List.for_all (Var.is_node) (CF.fv f) in *)
  (* we build the base pair for heap only
     after that, we compute the inv of the arith
  *)
  check_sat_from_data pdecls is_shape_only is_link_back_heap_only
      is_sat_check eager get_cex root_data bound t_size
  (* let t = new T.cyclic pdecls root *)
  (*   is_shape_only  (not is_shape_only) is_link_back_heap_only is_sat_check get_cex *)
  (*   (eager && is_sat_check) bound in *)
  (* try *)
  (*   let () = t # build_proof () in *)
  (*   t # find_satisfiability () *)
  (* with e -> begin *)
  (*     match e with Invalid_argument s -> *)
  (*     let () = print_endline_quiet ("S2S:" ^ s) in *)
  (*     Out.UNKNOWN, [],[] *)
  (*       | _ -> Out.UNKNOWN, [],[] *)
  (* end *)

(*
- find base triples for every ind preds
- combine them

collect sat
precise/over (quan-preds bases, buds)
arith computation
*)
let check_sat_x pdecls f0 eager bound t_size=
  let slTree_call is_shape_only is_link_back_heap_only f=
    let res,cex,_ = build_base_pair_or_sat pdecls is_shape_only is_link_back_heap_only true eager false f bound t_size in
    (res, cex)
  in
  let rec check_sat_aux is_shape_only is_link_back_heap_only fs=
    match fs with
      | f::rest -> begin
          let () = Debug.ninfo_hprint (add_str  " build_base_pair f" (CF.string_of)) f no_pos in
          let root_data = SlNode.mk_data pdecls true f in
          let res = SlNode.SL_NODE_DATA.eval_all is_shape_only root_data in
          (* let () = print_endline_quiet ("SLSAT:" ^ (Out.string_of res)) in *)
          if res == Out.UNSAT then
            check_sat_aux is_shape_only is_link_back_heap_only rest
          else res, [f]
        end
      | [] -> Out.UNSAT, []
  in
  let rec dep_partition vns eqs res=
    match vns with
      | vn::rest -> begin
          let vs = Var.get_eq_closure eqs vn.PeN.hpred_arguments in
          let () = Debug.ninfo_hprint (add_str  "vs" (Var.string_of_list)) vs no_pos in
          let grps, others = List.partition (fun (grp_vns,grp_vs)  ->
                Var.intersect grp_vs vs != []
          ) res in
          let new_res= match grps with
            | x::_ -> let merge_grps = List.fold_left (fun (r1,r2) (vns2, vs2) -> (r1@vns2,r2@vs2) ) ([vn], vs) grps in
              others@[(merge_grps)]
            | [] ->  (res@[([vn], vs)])
          in
          let () = Debug.ninfo_hprint (add_str  "new_res" (pr_list (pr_pair (pr_list PeN.string_of) Var.string_of_list))) new_res no_pos in
          dep_partition rest eqs new_res
        end
      | [] -> res
  in
  let rec check_sat_sub_form is_shape_only is_base_reuse and_fs last_sat=
    match and_fs with
      | f::rest -> begin
          if not is_base_reuse then (* not composition *)
            slTree_call is_shape_only (is_shape_only) f
          else
            let or_fs=
              CfUtil.unfold_base_pair pdecls false f
            in
            let res,cex = check_sat_aux is_shape_only (is_shape_only) or_fs in
            if res == Out.UNSAT then res,cex
            else check_sat_sub_form is_shape_only is_base_reuse rest (res,cex)
        end
      | [] -> last_sat
  in
  let rec aux_single ls done_ls res=
    match ls with
      | ((vn, src, _) as r)::rest -> if List.for_all (fun (_, src1, _) ->
          Var.intersect src src1 == []
        ) (rest@done_ls) then
          aux_single rest done_ls (res@[r])
        else aux_single rest (done_ls@[r]) (res)
      | [] -> res
  in
  let qvars, bare_f = CF.split_quantifiers f0 in
  let qvars1, p_qvars = List.partition (fun v -> not(is_node_typ v.Var.t)) qvars in
  let f = if qvars1!=[] then CF.add_quantifiers qvars1 bare_f
  else bare_f in
  let () = if p_qvars !=[] then
    (* Gen.print_endline_quiet "WARN: remove pointer-typed ex quantifiers before sat checking" *) ()
  else () in
  let _, vns, _, p = CF.decompose f in
  (* let is_deci = List.for_all ( fun decl -> *)
  (*       decl.Cpred.pred_is_sat_deci *)
  (* ) pdecls *)
  (* in *)
  let is_deci = List.for_all ( fun vn ->
      try
        let decl = List.find (fun def ->
                Ustr.str_eq def.Cpred.pred_name vn.CpredNode.hpred_name
        ) pdecls in
        decl.Cpred.pred_is_sat_deci
      with Not_found -> false
  ) vns
  in
  let is_compos = List.for_all ( fun decl ->
          decl.Cpred.pred_is_composable
            (* | Some (ls, _) -> ls!=[] *)
            (* | None -> false *)
  ) pdecls
  in
  (* is shape only? *)
  (*   let svs = CP.fv p in *)
  (* let is_shape_only =  List.for_all Var.is_node (qvars@svs) in *)
  let is_shape_only = List.for_all (fun p -> p.Cpred.pred_is_shape_only) pdecls in
  let and_fs = if (List.length vns) > 1 && is_deci && is_compos && is_shape_only
  then
    let fs1=
      let _,_, eqs, neqs, _ = CP.type_decomp p in
      let eqs = List.filter (fun (v1, v2) -> not (Var.equal v1 v2) ) eqs in
      let f,vns,eqs,neqs = if eqs==[] then f,vns,eqs,neqs else
        let f1 = CF.subst eqs f in
        let f2 = CF.simplify_pure f1 in
        let _, vns, _, p = CF.decompose f2 in
        let _,_, eqs, neqs, _ = CP.type_decomp p in
        f2, vns,eqs, neqs
      in
      let vns_groups = dep_partition vns eqs [] in
      let () = Debug.ninfo_hprint (add_str  "vns_groups" (pr_list_ln (pr_pair (pr_list PeN.string_of) Var.string_of_list))) vns_groups no_pos in
      let single_vns = List.fold_left (fun r (vns, _) ->
          if List.length vns == 1 then
            r@vns
          else  r
      ) [] vns_groups in
      let () = Debug.ninfo_hprint (add_str  "single_vns" (pr_list PeN.string_of)) single_vns no_pos in
      let vns_src_tar, srcs, tars = List.fold_left (fun (r1,r2,r3) vn ->
          let srcs, tars = Cpred.get_root_src_tar_acyclic pdecls vn.PeN.hpred_name vn.PeN.hpred_arguments in
          (r1@[(vn, srcs, tars)], r2@srcs,r3@tars)
      ) ([], [], []) vns in
      let () = Debug.ninfo_hprint (add_str  "srcs" (pr_list Var.string_of)) srcs no_pos in
      let () = Debug.ninfo_hprint (add_str  "tars" (pr_list Var.string_of)) tars no_pos in
      let single_src_vns = aux_single vns_src_tar [] [] in
      (* let diseq_vars = Var.remove_dups (List.fold_left (fun r (v1, v2) -> *)
      (*     r@[v1;v2]) [] neqs) in *)
      let haft_connected_vns = List.fold_left (fun r (vn, s, _) ->
          if Var.intersect s tars == []
            &&
            (* only applied for singly-linked lists *)
            List.length vn.PeN.hpred_arguments == 2
            (* not (List.exists (fun v1 -> *)
            (*     List.exists (fun v2 -> Var.equal v1 v2) s) diseq_vars) *)
          then r@[vn] else r
      ) [] single_src_vns in
      (* let haft_connected_vns = if haft_connected_vns == [] then [] *)
      (* else List.fold_left (fun r (v1, v2) -> *)
      (*     (\*if v1, v2 are two srcs, remove it*\) *)
      (* ) haft_connected_vns neqs *)
      (* in *)
      let () = Debug.ninfo_hprint (add_str  "haft_connected_vns" (pr_list PeN.string_of)) haft_connected_vns no_pos in
      let () = Debug.ninfo_hprint (add_str  "eqs" (pr_list Var.string_of_pair)) eqs no_pos in
      let useless_vns = if eqs==[] then (haft_connected_vns@single_vns)
      else [] in
      let f1 = List.fold_left (fun r vn ->
          CF.subtract_pred r vn) f useless_vns
      in
      let () = Debug.ninfo_hprint (add_str  "f1" (CF.string_of)) f1 no_pos in
      let fs2 = List.map (fun (grp_vns, _) ->
          let f2 =  List.fold_left (fun r vn ->
              CF.subtract_pred r vn) f1 (Gen.BList.difference_eq PeN.equal vns grp_vns)
          in
          (* discard useless neqs *)
          (* let vargs = List.fold_left (fun r vn -> r@(vn.PeN.hpred_arguments)) [] grp_vns in *)
          (* let vargs1 = Var.remove_dups ( vargs) in *)
          (* let () = Debug.ninfo_hprint (add_str  "vargs1" (Var.string_of_list)) vargs1 no_pos in *)
          (* let f3 = CF.subtract_useless_diseq f2 vargs1 in *)
          (* let () = Debug.ninfo_hprint (add_str  "f3" (CF.string_of)) f3 no_pos in *)
          f2
      ) (List.sort (fun (a1,_) (a2,_) -> (List.length a2) - (List.length a1)) vns_groups) in
      fs2
    in
    fs1
  else [f] in
  let () = Debug.ninfo_hprint (add_str  "and_fs" (pr_list CF.string_of)) and_fs no_pos in
  let is_base_reuse = !VarGen.sat_base_reuse && (not is_shape_only  && is_deci ) in
  let () = Debug.ninfo_hprint (add_str  "is_base_reuse" (string_of_bool)) is_base_reuse no_pos in
  let () = Debug.ninfo_hprint (add_str  "is_shape_only" (string_of_bool)) is_shape_only no_pos in
  let res,cex = check_sat_sub_form  is_shape_only is_base_reuse and_fs (Out.UNKNOWN, []) in
  res, None

let check_sat pdecls f eager bound t_size=
  let pr1 = CF.string_of in
  let pr3 = pr_pair Out.string_of (pr_option pr1) in
  Debug.no_2 "sl.check_sat" pr1  string_of_int pr3
      (fun _ _ -> check_sat_x pdecls f eager bound t_size) f bound
