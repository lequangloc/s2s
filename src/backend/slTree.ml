open Globals
open Gen
open VarGen

open Com

module CF = Cformula

module EN = SlNode
module N = SlNode.SLNODE
module E = SlEdge.SLEDGE

module BL = StrEdge.STREDGE

module PN = CpredNode

module SL_SUBTERM_ELT = struct
  type t = PN.t
  let string_of = PN.string_of

  let equal = PN.equal
end;;

module SUBT = Subterm.FSubTerm(SL_SUBTERM_ELT)


class ['t] cyclic pdecls init is_heap_only is_multi_domains
  is_link_back_heap_only is_sat_check
  get_cex is_return_first_sat b t_size = object(self)
  val mutable m_root: 't = init
  val mutable m_next_id = 1
  val m_pdecls = pdecls
  val m_bheap_only = is_heap_only
  val m_bmulti_domains = is_multi_domains
  val m_blink_back_heap_only = is_link_back_heap_only
  val m_bsat_check = is_sat_check (* not compute base *)
  val m_bget_cex = get_cex
  val m_bound = b
  val m_breturn_first_sat = is_return_first_sat
  val mutable m_nodes: 't array = Array.make t_size init
  val mutable m_edges : E.t list = []
  val mutable m_back_links:  BL.t list = []


  val mutable m_leaves: int list = []
  val mutable m_termination: bool = true

 (* for back-link construction *)
  val mutable m_subterm_map: SUBT.t list = []
    (* companion candidates*)
  val mutable m_reduced_nodes: int list = []

  (* eval a node and set its status accordingly *)
  method eval (e: 't) =
    let () = Debug.ninfo_hprint (add_str  "sl_tree.eval" N.string_of) e no_pos in
    let o = N.eval m_pdecls m_bheap_only  e in
    let () = Debug.ninfo_hprint (add_str  "sl_tree.eval" Out.string_of) o no_pos in
    o

  method eval_all (e: 't) =
    let o = N.eval_all (not m_bmulti_domains) e in
    let () = Debug.ninfo_hprint (add_str  "sl_tree.eval_all" Out.string_of) o no_pos in
    o

  method string_of ()=
    let rec helper n s=
      if n < m_next_id then
        let s = s ^ (N.string_of (Array.get m_nodes n)) ^ "\n" in
        helper (n+1) s
      else s
    in
    let s = "" in
    (* node *)
    let s = s ^ "nodes:\n" in
    let s = helper 0 s in
    (* edge *)
    let s = s ^ "\nedges:\n" in
    let s = List.fold_left (fun r e->
        r ^ (E.string_of e) ^ "\n"
    ) s m_edges in
    (* back-links *)
    let s = s ^ "\nback-links:" in
    let s = List.fold_left (fun r e->
        r ^ (BL.string_of e)  ^ "\n"
    ) s m_back_links in
    s

  method get_node id=
    Array.get m_nodes id

  method get_root ()=
    self#get_node (root_parent_ID + 1)

  method get_height id=
    let n = self#get_node id in
    n.N.height

  method update_subterm (view:PN.t) (sub_views: PN.t list) =
    let rec lookup_and_insert v ls sub_done=
      match ls with
        | [] -> false, sub_done
        | xs::sub_rest ->
              if SUBT.mem view xs then
                let up_subterms = SUBT.append xs sub_views in
                true, sub_done@[up_subterms]@sub_rest
              else lookup_and_insert view sub_rest (sub_done@[xs])
    in
    let res, ls = lookup_and_insert view m_subterm_map [] in
    let new_map = if res then ls
    else ls@[SUBT.mk ([view]@sub_views)]
    in
    m_subterm_map <- new_map

  method link_back n=
    let rec is_eq_univ_vars_x bud_qvars comp_qvars sst=
      match sst with
        | (b_arg, c_arg)::rest -> begin
            let b1 =  Var.mem b_arg bud_qvars in
            let b2 =  Var.mem c_arg comp_qvars in
            match b1, b2 with
              | true, true -> is_eq_univ_vars_x bud_qvars comp_qvars rest
              | false, true
              | true, false -> false
              | false, false -> if Var.equal b_arg c_arg then
                  is_eq_univ_vars_x bud_qvars comp_qvars rest
                else false
          end
        | [] -> true
    in
    let is_eq_univ_vars bud_qvars comp_qvars sst=
      let pr1 = Var.string_of_list in
      let pr2 = pr_list (pr_pair Var.string_of Var.string_of) in
      Debug.no_3 "is_eq_univ_vars" pr1 pr1 pr2 string_of_bool
          (fun _ _ _ -> is_eq_univ_vars_x bud_qvars comp_qvars sst)
          bud_qvars comp_qvars sst
    in
    let rec find_incr acc_bud_views (cview, comp_qvars, bud_qvars, is_empty_univ_pred) done_bud_views=
      match acc_bud_views with
        | bv::rest ->
              let () = Debug.ninfo_hprint (add_str  "link_back (bv.PN.hpred_name)"
                  PN.string_of) bv no_pos in
              let () = Debug.ninfo_hprint (add_str  "is_empty_univ_pred"
                  string_of_bool) is_empty_univ_pred no_pos in
              if Ustr.str_eq cview.PN.hpred_name bv.PN.hpred_name then
                if is_empty_univ_pred || is_eq_univ_vars bud_qvars comp_qvars (List.combine bv.PN.hpred_arguments cview.PN.hpred_arguments) then
                  bv,done_bud_views@rest
                else find_incr rest (cview, comp_qvars, bud_qvars,is_empty_univ_pred) (done_bud_views@[bv])
              else find_incr rest (cview, comp_qvars, bud_qvars,is_empty_univ_pred) (done_bud_views@[bv])
        | [] -> raise Not_found
    in
    let () = Debug.ninfo_hprint (add_str  "link_back (bud)"
        N.string_of) n no_pos in
    let bud_univ_ptos = EN.get_univ_ptos n.N.data in
    let bud_qvars, bud_views, bud_univ_views = EN.get_univ_preds n.N.data in
    let rec do_link ls=
      match ls with
        | [] -> false
        | id::rest -> begin
             (* do not link with itself *)
            if id == n.N.id then do_link rest else
              let comp = Array.get m_nodes id in
              let () = Debug.ninfo_hprint (add_str  "link_back (comp)"
 (N.string_of)) comp no_pos in
              if not ((EN.qf_equal n.N.data comp.N.data)) then do_link rest else
              let comp_univ_ptos = EN.get_univ_ptos comp.N.data in
              let comp_qvars, comp_views, comp_univ_views = EN.get_univ_preds comp.N.data in
              if (List.length comp_univ_ptos) = (List.length bud_univ_ptos) &&
                (* Var.diff comp_univ_ptos bud_univ_ptos = [] *)
                (List.for_all (fun v1 -> List.exists (fun v2 -> Var.equal v1 v2) bud_univ_ptos) comp_univ_ptos) &&
                List.length bud_views >= List.length comp_views then
                  try
                    let is_empty_univ_pred = (comp_univ_views==[] && bud_univ_views==[])in
                    let sst, is_subterm, matched_bud_views, rest_bud_views = List.fold_left (fun (acc_sst, acc_sub, acc_matched_bud_views, acc_bud_views) cview ->
                        let () = Debug.ninfo_hprint (add_str  "link_back (cview.PN.hpred_name)"
                            pr_id) cview.PN.hpred_name no_pos in
                        let bview, rest_bud_views = find_incr acc_bud_views (cview, comp_qvars, bud_qvars, is_empty_univ_pred) []
                          (* List.find (fun bv -> *)
                        (*       let () = Debug.ninfo_hprint (add_str  "link_back (bv.PN.hpred_name)" *)
                        (*           pr_id) bv.PN.hpred_name no_pos in *)
                        (*       if Ustr.str_eq cview.PN.hpred_name bv.PN.hpred_name then *)
                        (*         is_empty_univ_pred || is_eq_univ_vars bud_qvars comp_qvars (List.combine bv.PN.hpred_arguments cview.PN.hpred_arguments) *)
                        (*       else false *)
                        (* ) acc_bud_views *) in
                        let  sst = List.fold_left (fun (acc) (v1,v2) ->
                            let acc1 = (* if not (Var.equal v1 v2) then *) acc@[(v1,v2)] (* else acc *) in
                            (acc1)
                        ) ([]) (List.combine cview.PN.hpred_arguments bview.PN.hpred_arguments) in
                        let is_global_sound = (* if m_bheap_only then *)
                        (*   (\* do not link with itself *\) *)
                        (*   cview.PN.hpred_unfold_num != bview.PN.hpred_unfold_num *)
                        (* else *)
                          (*********TLL*******)
                          (* cview.PN.hpred_unfold_num < bview.PN.hpred_unfold_num *)
                          true in
                        let is_sub = is_global_sound (* if not is_global_sound then false else *)
                          (* (\* compare qf_eq *\) *)
                          (* EN.qf_equal n.N.data comp.N.data *)
                        in
                        (acc_sst@sst, acc_sub || is_sub, acc_matched_bud_views@[bview], rest_bud_views)
                    ) ([], false, [], bud_views) comp_views
                    in
                    if not ((* m_bheap_only || bug at 19-e05 *) is_subterm ) then
                      do_link rest
                    else
                       (* as comp may not be bud's ancestor, check whether all quantified heaps of comp is
                      isomophic (subsumed by ) to bud*)
                      let is_subsumed_quantified_heap = not is_empty_univ_pred || 
                        EN.is_quantified_subsumed_views n.N.data comp.N.data in
                      if not is_subsumed_quantified_heap then do_link rest
                    else
                      (* sst is consistent? *)
                      let sst = (Gen.BList.remove_dups_eq (* Var.equal_pair_vars *)
                          (fun (v1, v2) (v3, v4) -> Var.equal v1 v3 && Var.equal v2 v4)
                          (List.filter (fun (v1,v2) -> not( Var.equal v1 v2)) sst)) in
                      let () = Debug.ninfo_hprint (add_str  "sst"
 (pr_list Var.string_of_pair)) sst no_pos in
                      let src_vars = List.map fst sst in
                      let src_vars1 = Var.remove_dups src_vars in
                      let () = Debug.ninfo_hprint (add_str  "src_vars"
                          (pr_list Var.string_of)) src_vars no_pos in
                       let () = Debug.ninfo_hprint (add_str  "src_vars1"
                          (pr_list Var.string_of)) src_vars1 no_pos in
                      (* let all_tar_sst1 = Var.remove_dups all_tar_sst in *)
                      if (sst == [] ||
                          (((List.length src_vars1) == (List.length src_vars))(*  && *)
                      (* ( (List.length all_tar_sst1) == (List.length all_tar_sst)) *)))  then
                        let is_arith_implied = if m_blink_back_heap_only then true
                          else
                            let comp_arith1 = Cpure.subst_var sst (EN.get_node_arith comp.N.data) in
                            let bud_arith1 = (EN.get_node_arith n.N.data) in
                            m_bheap_only || (Com.is_imply bud_arith1 comp_arith1)
                        in
                        if not is_arith_implied then
                          do_link rest
                        else
                      (* check whether rest_bud_views is relatively complete wrt. matched_bud_views*)
                        (* if not (SlUtil.is_relative_complete bud_qvars rest_bud_views matched_bud_views) then do_link rest *)
                        (* else *)
                        (* add a back link*)
                        let back_link = {BL.from_id = n.N.id;
                        BL.to_id = id;
                        BL.label = List.map (fun (v1, v2) -> (v1, Exp.Var (v2, no_pos)) ) sst;
                        } in
                        let s = if List.length bud_views > List.length comp_views then NcycleCC else Ncycle in
                          let () = n.N.status <- s in
                          let () = m_back_links <- m_back_links@[back_link] in
                          true
                      else do_link rest
                  with Not_found -> do_link rest
              else do_link rest
          end
    in
     let res= (* if n.N.parent == root_parent_ID then *)
    (*   false (\* root *\) *)
    (* else *)
      if List.for_all (fun vn -> vn.PN.hpred_unfold_num == 0) bud_views then
        (* no progress *)
        if !VarGen.sat_early_detect_non_progress && m_breturn_first_sat && (List.for_all (fun pred -> not (Cpred.is_progressing pred)) m_pdecls) then raise Com.EARLY_SAT_DECT_EXC
        else
          false
      else
        do_link m_reduced_nodes
    in
    let () = Debug.ninfo_hprint (add_str  "link_back (output)"
        (string_of_bool)) res no_pos in
    res


  method complete (e)=
    let () = Debug.ninfo_hprint (add_str  "tree.complete.input" SlNode.SL_NODE_DATA.string_of_short) e no_pos in
    let res = EN.unfold_bfs m_pdecls m_breturn_first_sat m_bheap_only e in
    let res1 = List.map (fun (e1, (view, sub_f, sub_views)) ->
        let () = self # update_subterm view sub_views in
        (e1, (view, sub_f))
    ) res in
    res1

  method construct_child parent child_entries=
    let children = List.map (fun (en, subs) ->
        let id = m_next_id in
        let () = m_next_id <- m_next_id + 1 in
        let child = N.mk id en parent.N.id []
          (parent.N.height + 1) Nopen in
        let new_edge = E.mk parent.N.id id [subs] in
        let () = m_edges <- m_edges @[new_edge] in
        (* update parent *)
        let () = parent.N.child <- parent.N.child @ [id] in
        (* update global data *)
        let () = Array.set m_nodes id child in
        child
    ) child_entries in
    children

  method unfold (e: 't)=
    let () = Debug.ninfo_hprint (add_str  "tree.unfold.input" N.string_of) e no_pos in

    let child_ews = self#complete e.N.data in
    child_ews

  method lookup_open ls=
    match ls with
        | [] -> (false, None, [])
        | cur::tl -> begin
            (* eval *)
            let o = self#eval cur in
            if m_breturn_first_sat && o = Out.SAT && ((not m_bmulti_domains) || (self#eval_all cur) = Out.SAT) then
              (true, None, tl)
            else if o = Out.SAT || o = Out.SATCM ||
              o = Out.UNSAT then
              (* move to next *)
              self#lookup_open tl
            else if self#link_back cur then
              self#lookup_open tl
            else (false, Some cur, tl)
          end

  method build_iter bound onodes=
    if bound <= 0 then
      let () = m_termination <- false in
      ()
    else
      let met_sat, cur_opt, rest = self#lookup_open onodes in
      if met_sat then () else
      match cur_opt with
        | Some cur ->
              (* back link *)
              (* unfold *)
              let child_ews = self#unfold cur in
              let new_opens = if child_ews == [] then
                let () = cur.N.status <- Nunsat in
                rest
              else
                let children = self#construct_child cur child_ews in
                (* let base_child_ews, rest_child_ews = List.partition ( *)
(* fun (d, _) -> EN.is_base_node d ) child_ews in *)
                (*               let base_children = self#construct_child cur base_child_ews in *)
                (*               let rest_children = self#construct_child cur rest_child_ews in *)
                let () = cur.N.status <- Nreduced in
                let new_opens = children @ rest in
                new_opens
              in
              let () = m_reduced_nodes <- m_reduced_nodes@[cur.N.id] in
              (* let new_opens = ((base_children @ rest_children) @ rest) in *)
              (* let new_opens = (base_children @ rest_children) in *)
              self # build_iter (bound - 1) new_opens
        | None ->
              let () = Debug.ninfo_hprint (add_str  "No more open leaf" string_of_int) (m_bound - bound) no_pos in
              () (*END*)

  method build_proof ()=
    let () = m_next_id <- init.N.id + 1 in
    (*simplify m_root?*)
    (* add root into the first of m_nodes *)
    let () = Array.set m_nodes 0 m_root in
    let () =  self # build_iter m_bound [m_root] in
    let () = Debug.ninfo_hprint (add_str  "subterm_map" (pr_list (SUBT.string_of))) m_subterm_map no_pos in
    let () = if !VarGen.sat_show_proof then
      let () = Debug.info_hprint (add_str  "tree" pr_id) (self#string_of()) no_pos in
      ()
    else ()
    in
    ()

  method lookup_leaf ()=
    let rec aux id res=
      if id < m_next_id then
        let n = Array.get m_nodes id in
        if n.N.child == [] then
          aux (id+1) (res@[id])
        else aux (id+1) res
      else res
    in
    let leaves = aux 0 [] in
    let () = m_leaves <- leaves in
    leaves

  method lookup_leaf_children id=
    let rec aux ids done_ids res=
      match ids with
        | id::rest ->
              let n = self#get_node id in
              if n.N.child == [] then
                aux rest (done_ids@[id]) (res@[id])
              else
                aux (rest@n.N.child) (done_ids@[id]) res
        | [] -> res
    in aux [id] [] []

  method find_satisfiability_combined_doms sat_leaf_nodes0=
    (* filter unsat *)
    let unsat_leaves, sat_leaf_nodes1 = List.fold_left (fun (r1,r2) n ->
        let o = self#eval_all n in
        if o == Out.UNSAT then
          let () = n.N.status <- Nunsat in
          (r1@[n], r2)
        else (r1, r2@[n])
    ) ([], []) sat_leaf_nodes0 in
    let () = Debug.ninfo_hprint (add_str  "unsat_leaves" (pr_list_ln N.string_of))
      (unsat_leaves) no_pos in
    if sat_leaf_nodes1 == [] then [], [] else
      (* remove bls with the same companion *)
        let bls = Gen.BList.remove_dups_eq (fun bl1 bl2 ->
            bl1.BL.to_id = bl2.BL.to_id
        ) m_back_links in
      (* overllaped cycles -> unknown *)
      if List.length bls > 1 then
        (*TODO: *)
        sat_leaf_nodes0, []
      else
        let () = Debug.ninfo_hprint (add_str  "bls" (pr_list_ln BL.string_of)) bls  no_pos in
        (* sat leaf belongs to cycle: more than one --> unknown *)
        let pr_bls = List.fold_left (fun r bl ->
            let leaf_child = self#lookup_leaf_children bl.BL.to_id in
            (*remove bud*)
            let leaf_child1 = List.filter (fun id -> id != bl.BL.from_id) leaf_child in
            if leaf_child1 == [] then r else
              r@[(bl.BL.to_id, leaf_child1)]
        ) [] bls in
        let () = Debug.ninfo_hprint (add_str  "sat_leaf_nodes1" (pr_list_ln N.string_of))
          (sat_leaf_nodes1) no_pos in
        (* a combined leaf = heap of leaf node + arith of comp *)
        let ind_sat_leaves, pr_leaf_cycles = List.fold_left (fun (r1, r2) (comp_id, ls_sat_ids)->
            let leaves, nr1 = List.partition (fun n -> List.exists (fun id1 -> id1 = n.N.id) ls_sat_ids) r1 in
            nr1, r2@([(comp_id, leaves)])
        ) (sat_leaf_nodes1, []) pr_bls in
        let () = Debug.ninfo_hprint (add_str  "ind_sat_leaves" (pr_list_ln N.string_of))
          (ind_sat_leaves) no_pos in
        let () = Debug.ninfo_hprint (add_str  "pr_leaf_cycles" (pr_list_ln (pr_pair string_of_int (pr_list_ln N.string_of))))
          (pr_leaf_cycles) no_pos in
        (*do_combine*)
        let is_complete, leaf_cycles = List.fold_left (fun (r1, r2) (comp_id, leaves) -> begin
          match leaves with
            | [leaf] ->
                  let comp = self#get_node comp_id in
                  let comp_a = comp.N.data.EN.SL_NODE_DATA.arith in
                  let comp_a_qvars = Var.intersect comp.N.data.EN.SL_NODE_DATA.qvars (Var.remove_dups (Cpure.fv comp_a.EN.SL_NODE_DATA.arith_pure)@(Cpure.fv comp_a.EN.SL_NODE_DATA.inv_preds))in
                  let n_data = {leaf.N.data with EN.SL_NODE_DATA.qvars = comp_a_qvars;
                      EN.SL_NODE_DATA.arith = comp_a} in
                  let n_leaf = {leaf with N.data = n_data} in
                  (r1, r2@[n_leaf])
            | [] -> (r1, r2)
            | _ -> (false, leaves)
        end
        ) (true, []) pr_leaf_cycles in
        if not is_complete then sat_leaf_nodes0, [] else
          [], ind_sat_leaves@leaf_cycles

   method find_sat_heap_leaves ()=
     let leaves = self # lookup_leaf () in
     let sat_leaves, buds = List.fold_left (fun (r,r2) id ->
         let n =  Array.get m_nodes id in
         if (n.N.status == Nsat) then
           (* if m_bheap_only then *)
           (r@[n],r2)
               (* else if *)
               (*   let () = Debug.ninfo_hprint (add_str  "eval_all" (pr_id)) *)
               (* ("1") no_pos in *)
               (*   (self#eval_all n) == SAT then r@[n],r2 *)
               (* else (r,r2) *)
         else if (n.N.status == NsatCC) then
           (* let () = Debug.ninfo_hprint (add_str  "eval_all" (pr_id)) *)
           (*   ("2") no_pos in *)
           (* let o = self#eval_all n in *)
           (*syntax*)
           if  m_bmulti_domains && (self#eval_all n) == Out.UNSAT then r,r2
           else if m_bheap_only || SlNode.syntax_complete_bud n.N.data then
             let () = n.N.status <- Nsat in
             r@[n],r2
           else
             let () = n.N.status <- Nincompl in
             r,r2
                 (* semantic *)
         else if (n.N.status == Ncycle || ( m_bheap_only && n.N.status == NcycleCC) ) then r,r2@[n] else r,r2
     ) ([],[]) leaves in
     let () = Debug.ninfo_hprint (add_str  "cexes" (pr_list_ln N.string_of))
       ((* List.map (fun id -> Array.get m_nodes id) *) sat_leaves) no_pos in
     leaves, sat_leaves, buds

  method find_satisfiability ()=
    let leaves, sat_leaves, buds = self # find_sat_heap_leaves () in
    let () = Debug.ninfo_hprint (add_str  "is_sat_check" (string_of_bool))
        is_sat_check no_pos in
    let leaves, sat_leaves = if not m_bmulti_domains || is_sat_check then
      leaves, sat_leaves
    else
      let leaves,lnodes = self # find_satisfiability_combined_doms sat_leaves in
      let () = Debug.ninfo_hprint (add_str  "lnodes" (pr_list_ln N.string_of))
        (lnodes) no_pos in
      List.map (fun n -> n.N.id) leaves, lnodes
    in
     let () = Debug.ninfo_hprint (add_str  "sat_leaves" (pr_list_ln N.string_of))
        sat_leaves no_pos in
    if not m_termination then (Out.UNKNOWN, [],[]) else
    (* sat *)
      if sat_leaves != [] then
        let () = Debug.ninfo_hprint (add_str  "m_bget_cex" string_of_bool)
            (m_bget_cex) no_pos in
        let sat_leaves, buds = if m_bget_cex then
          let sat_leaves = List.map (fun n -> SlNode.star_compose_univ  n.N.data) sat_leaves in
          let buds = List.map (fun n -> SlNode.star_compose_univ  n.N.data) buds in
          sat_leaves, buds
        else [], []
        in
        let () = if !VarGen.show_cex then
          let () = Debug.info_hprint (add_str  "cexes" (pr_list_ln CF.string_of))
            ((* List.map (fun id -> Array.get m_nodes id) *) sat_leaves) no_pos in ()
        else ()
        in
        (Out.SAT, BList.remove_dups_eq CF.equal sat_leaves, BList.remove_dups_eq CF.equal buds)
      else if List.for_all (fun id ->
          let n =  Array.get m_nodes id in
          (n.N.status == Nunsat) || (n.N.status == Ncycle) || (n.N.status == NcycleCC)
      ) leaves then
        (Out.UNSAT, [], [])
      else (Out.UNKNOWN, [], [])


end;;
