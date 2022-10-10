open Globals
open Gen
open VarGen

open EntType
open Com

module SUBT = EntType.SUBT
open EntType.SL_SUBTERM_ELT

module CF = Cformula
module PN = CpredNode
module CPoN = CptoNode
module CP = Cpure

module SLN = SlNode
module SLND = SlNode.SL_NODE_DATA

module EN = EntNode
module N = EntNode.ENTNODE
module E = EntEdge.ENTEDGE

module BL = StrEdge.STREDGE

module ER = EntRule
module EC = EntCyc


class ['t] cyclic_forest pdecls init ass is_linear
  is_heap_only is_rhs_ex_quans is_base_reuse
  is_complete b = object(self)
  val mutable m_root: 't = init
  val mutable m_next_node_id = 1
  val m_pdecls = pdecls
  val m_bcomplete = is_complete
  val m_bound = b
  val m_bheap_only = is_heap_only
  val m_rhs_ex_quans = is_rhs_ex_quans
  val m_btw = is_base_reuse
  val mutable m_assumptions = ass
  val mutable m_nodes: 't array = Array.make (if is_linear then tree_size else tree_size_big)  init
  val mutable m_edges : E.t list = []
  val mutable m_back_links:  BL.t list = []


  val mutable m_leaves: int list = []
  val mutable m_termination: bool = true

 (* for back-link construction *)
  val mutable m_subterm_map: SUBT.t list = []
    (* companion candidates*)
  val mutable m_reduced_nodes: int list = []

  val mutable m_ctrees: EntTree.cyc_tree array = Array.make
    (if is_linear then proof_size else proof_size_big) (EntTree.dump_tree )
  val mutable m_waiting_ctrees = []
  val mutable m_invalid_ctrees = []
  val mutable m_working_ctree : int = 0

  (* proof search*)
  val m_ps_fnc =
    if is_linear && not is_rhs_ex_quans then
      PsLinCo.ps_col
    else
      if is_rhs_ex_quans && not is_heap_only then
        PsEx.ps_ex
      else
        PsGen.proof_search

  val m_abd_sat_fnc =
    if is_linear && not is_rhs_ex_quans then
      Abd.arith_sat_id
    else
      if is_base_reuse && is_heap_only then
        Abd.arith_sat_id else
        if is_rhs_ex_quans && not is_heap_only then
          Abd.arith_sat_abduce
        else
          Abd.arith_sat_id

  (* eval a node and set its status accordingly *)
  method eval (e: 't) =
    let () = Debug.ninfo_hprint (add_str  "ent_tree.eval id" string_of_int) e.N.id no_pos in
    let o, ass = N.eval_ent m_pdecls m_bheap_only m_assumptions  e in
    let () = m_assumptions <- m_assumptions@ass in
    let () = Debug.ninfo_hprint (add_str  "ent_tree.eval" Out.string_of) o no_pos in
    o

  method eval_all (e: 't) =
    let o = N.eval_all m_bheap_only e in
    let () = Debug.ninfo_hprint (add_str  "ent_tree.eval_all" Out.string_of) o no_pos in
    o

  method string_of ()=
    let rec helper n s=
      if n < m_next_node_id then
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
    (* back-links *)
    let s = s ^ "\nassumptions:" in
    let s = List.fold_left (fun r ass->
        r ^ ((pr_pair CP.string_of CP.string_of) ass)  ^ "\n"
    ) s m_assumptions in
    s

  method get_node id=
    Array.get m_nodes id

  method get_tree id=
    Array.get m_ctrees id

  method set_tree id t=
    Array.set m_ctrees id t

  method get_root ()=
    self#get_node (root_parent_ID + 1)

  method get_height id=
    let n = self#get_node id in
    n.N.height

  method update_tree_nodes t_id new_node_ids=
    let () = Debug.ninfo_hprint (add_str "new_node_ids" (pr_list string_of_int)) new_node_ids no_pos in
    let tree = self#get_tree t_id in
    let () = tree.EntTree.m_node_ids <- (tree.EntTree.m_node_ids@new_node_ids) in
    ()

  method lookup_onodes t_id=
    let tree = self#get_tree t_id in
    List.fold_left (fun acc node_id ->
        let n = self#get_node node_id in
        if n.N.status == Nopen then acc@[n]
        else acc
    ) [] tree.EntTree.m_node_ids

  method get_waiting_tree_contain nid=
    let rec aux ls max_tid res=
      match ls with
        | tid::rest -> if tid < max_tid then
            let tree = self#get_tree tid in
            let n_res = if List.exists (fun id -> id = nid) tree.EntTree.m_node_ids then
              res@[tid]
            else res
            in aux rest max_tid n_res
          else res
        | [] -> res
    in aux m_waiting_ctrees (EntTree.get_cur_id ()) []

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
    let rec is_same_type_length comp_univ_ptos  bud_univ_ptos=
      match comp_univ_ptos with
        | x::_ ->
              let csame, crem = List.partition (fun p -> Ustr.str_eq x.CPoN.hdata_name p.CPoN.hdata_name  ) comp_univ_ptos in
              let bsame, brem = List.partition (fun p -> Ustr.str_eq x.CPoN.hdata_name p.CPoN.hdata_name  ) bud_univ_ptos in
              (List.length csame == List.length bsame) &&
                  (is_same_type_length crem brem)
        | [] -> bud_univ_ptos == []
    in
    let () = Debug.ninfo_hprint (add_str  "link_back (bud)"
        N.string_of) n no_pos in
    let bud = n.N.data in
    if bud.EN.ENT_NODE_DATA.b_lu || SLND.is_empty_heap_or_htrue bud.EN.ENT_NODE_DATA.cons ||
      bud.EN.ENT_NODE_DATA.fp == Cheap.HEmp then false,[] else
    let bud_qvars, bud_views, bud_ptos, bud_eql, bud_arith  = SLN.star_decompose bud.EN.ENT_NODE_DATA.ante in
    let bud_pure = SLND.to_pure bud.EN.ENT_NODE_DATA.ante in
    (* if List.for_all (fun vn -> vn.PN.hpred_unfold_num == 0) bud_views then *)
    (*   (\* no progress *\) *)
    (*   false, [] *)
    (* else *)
      let beqNulls, _, beqs, _ = (* CP.type_decomp bud_pure*) Eql.decompose bud_eql in
    let bud_univ_ptos, bud_univ_pto_vars = EN.get_univ_ptos bud_qvars beqs bud_ptos in
    let bud_univ_views = EN.get_univ_preds bud_qvars beqs bud_views in
    let rec do_link ls=
      match ls with
        | [] -> false,[]
        | id::rest ->begin
              let comp_n = Array.get m_nodes id in
              let comp = comp_n.N.data in
              let () = Debug.ninfo_hprint (add_str  "link_back (comp)"
 (N.string_of)) comp_n no_pos in
              let comp_qvars, comp_views, comp_ptos, comp_eql, comp_arith = SLN.star_decompose comp.EN.ENT_NODE_DATA.ante in
              let comp_pure = SLND.to_pure comp.EN.ENT_NODE_DATA.ante in
              let ceqNulls, _, ceqs, _  = Eql.decompose comp_eql (* CP.type_decomp comp_pure *) in
              let comp_univ_ptos, comp_univ_pto_vars = EN.get_univ_ptos comp_qvars ceqs comp_ptos  in
              let comp_univ_views = EN.get_univ_preds comp_qvars ceqs comp_views in
              if (List.length comp_univ_ptos) = (List.length bud_univ_ptos) (* && (is_same_type_length comp_univ_ptos  bud_univ_ptos) *) (* && *)
                (* Var.diff comp_univ_pto_vars bud_univ_pto_vars = [] *)  && (* matching and put in fp already*)
                 List.length bud_views >= List.length comp_views then
                  try
                    (* let is_empty_univ_pred = comp_univ_views==[] && bud_univ_views==[] in *)
                    let linked_pr_views, is_subterm, sst = EC.search_match_comp_views m_pdecls m_subterm_map comp_views comp_qvars bud_views bud_qvars
                    in
                    if is_subterm then
                      (* sst is consistent? *)
                      let src_vars, tar_vars = List.split sst in
                      let src_vars1 = Var.remove_dups src_vars in
                      if (List.length src_vars1) == (List.length src_vars) &&
                        (Var.intersect src_vars1 tar_vars ==[]) then
                          (* TODO: compare equal whole LHS of comp to (part) LHS of bud *)
                          let match_bud_ptos, sst2, rest_bud_ptos = EC.search_match_bud_pto m_bheap_only
                            (if m_bheap_only then [] else sst) comp_ptos comp_qvars ceqs
                            bud_ptos bud_qvars beqs in
                          (*check whether it contains a cycle subst*)
                          let match_pto_vs = List.fold_left (fun r dn -> r@([dn.CPoN.hpto_node])@dn.CPoN.hpto_arguments) [] match_bud_ptos in
                          if List.exists (fun (sv,_) -> Var.mem sv match_pto_vs) sst2 then do_link rest else
                            let sst2b = sst@sst2 in
                            let () = Debug.ninfo_hprint (add_str  "sst2b"
                                  (pr_list Var.string_of_pair)) sst2b no_pos in
                            let is_arith_implied, ass, sst3 = if m_bheap_only  then true, [],sst2b else
                              let sst2a = EC.unify_views_same_spatial sst2b comp.EN.ENT_NODE_DATA.cons bud.EN.ENT_NODE_DATA.cons in
                              let sst3 = sst2b@sst2a in
                              (* compare comp_arith[sst] ==> bud_arith *)
                              let comp_arith1 = CP.add_quantifiers (List.map (Var.subst sst3) comp_qvars) (CP.subst_var sst3 comp_arith) in
                              let () = Debug.ninfo_hprint (add_str  "comp_arith1"
                                  (CP.string_of)) comp_arith1 no_pos in
                              let () = Debug.ninfo_hprint (add_str  "bud_arith"
                                  (CP.string_of)) bud_arith no_pos in
                              (* let qvars = Var.diff (CP.fv comp_arith2) (CP.fv bud_arith) in *)
                              (* let comp_arith3 = CP.add_quantifiers qvars comp_arith2 in *)
                              let is_implied, ass = Abd.arith_abduce m_assumptions bud_arith comp_arith1 in
                              let () = m_assumptions <- m_assumptions@ass in
                              is_implied, ass, sst3
                            in
                            if not is_arith_implied then
                              do_link rest
                            else
                              let is_complete_linked = if rest_bud_ptos == [] && (List.length linked_pr_views) == (List.length bud_views) then
                                (* is RHS identical with sst@sst2? *)
                                EC.is_match_rhs_back_link (sst3) comp.EN.ENT_NODE_DATA.cons bud.EN.ENT_NODE_DATA.cons bud_univ_ptos bud.EN.ENT_NODE_DATA.fp
                              else
                                false
                              in
                              (* add a back link*)
                              let back_link = {BL.from_id = n.N.id;
                              BL.to_id = id;
                              BL.label = List.map (fun (v1, v2) -> (v1, Exp.Var (v2, no_pos)) ) sst;
                              } in
                              let s = if not is_complete_linked  then NcycleCC else Ncycle in
                              let () = n.N.status <- s in
                              let () = m_back_links <- m_back_links@[back_link] in
                              let leave = if is_complete_linked then
                                []
                              else
                                (* find a cut *)
                                let rhs_comp  = SLND.subst (sst@sst2) comp.EN.ENT_NODE_DATA.cons in
                                let n_leaves = ER.construct_ccut m_pdecls n.N.id comp_n.N.id (sst3)
                                  n.N.data (List.map snd linked_pr_views, match_bud_ptos, comp_pure, rhs_comp) in
                                n_leaves
                              in true, leave
                      else do_link rest
                    else do_link rest
                  with Not_found -> do_link rest
              else do_link rest
          end
    in
    let res, new_leave = if n.N.parent == root_parent_ID || bud_views ==[] then
      false, [] (* root or no pred on LHS of bud *)
    else
      let t = self#get_tree m_working_ctree in
      let cur_reduced_nodes = Gen.BList.intersect_eq (=) m_reduced_nodes t.EntTree.m_node_ids in
      do_link cur_reduced_nodes
    in
    let () = Debug.ninfo_hprint (add_str  "link_back (output)"
        (string_of_bool)) res no_pos in
    let () = Debug.ninfo_hprint (add_str  "link_back (output) complete"
        (string_of_bool)) (res && new_leave ==[]) no_pos in
    res, new_leave



  method complete (e)=
    let () = Debug.ninfo_hprint (add_str  "ent.proof_search.input" EntNode.ENT_NODE_DATA.string_of_short) e no_pos in
    let res, qvars_sst, is_stuck = m_ps_fnc (* ER.proof_search *) m_pdecls m_bheap_only  e in
    (* if LUNFOLD *)
    let is_lufold = List.fold_left ( fun r x ->
        let r1 =  List.fold_left (fun r (_, entR) -> begin
          let proofs = ER.flatten_proofs entR in
          let r2 = List.fold_left (fun r3 entR1 ->
              match entR1 with
                | EntRule.IR_LUNFOLD (vn, f) ->
                      let sub_views, _ = CF.star_decompose f in
                      if sub_views == [] then true else
                        let () = self # update_subterm vn sub_views in
                        true
                | _ -> r3
          ) r proofs in
          r2
        end ) false x
        in r1 || r
    ) false res in
    (* if qvars_sst - points-to matching and
       lhs qvars are instantiated,
       update substerm relationships *)
    let () = if qvars_sst == [] then () else
      let old_qvars = List.map fst qvars_sst in
      let new_subterm_map = List.map (fun m ->
          let new_vns = List.fold_left (fun r vn ->
              if Var.intersect old_qvars vn.PN.hpred_arguments != [] then
                let new_vn = PN.subst qvars_sst vn in
                r@[new_vn]
              else r
          ) [] m in
          m@new_vns
      ) m_subterm_map in
      let () = m_subterm_map <- new_subterm_map in
      () in
    res,is_lufold, is_stuck

  method construct_child parent child_entries=
    let children = List.map (fun (en, r) ->
        let id = m_next_node_id in
        let () = m_next_node_id <- m_next_node_id + 1 in
        let child = N.mk id en parent.N.id []
          (parent.N.height + 1) Nopen in
        let new_edge = E.mk parent.N.id id [r] in
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

    let child_ews, is_lufold,is_stuck = self#complete e.N.data in
    child_ews,is_lufold, is_stuck

  method lookup_open ls=
    match ls with
        | [] -> (None, None, [], [])
        | cur::tl -> begin
            (* eval *)
            let o = self#eval cur in
            if o = Out.INVALID then
              (Some cur, None, tl, [])
            else if o = Out.VALID then
              (* move to next *)
              self#lookup_open tl
            else
              (* check whether can do pred matching *)
              let is_pred_match = ER.is_match_pred m_pdecls cur.N.data in
              let is_linked, new_leave = if is_pred_match then
                (* do matching prior to linking back *)
                false, []
              else self#link_back cur in
              if is_linked then begin
                if new_leave ==[] then
                  self#lookup_open tl
                else (None, Some cur, tl, new_leave)
              end
              else (None, Some cur, tl, [])
          end

  method clone_tree tree_ids ls_new_nodes=
    let aux_clone new_node_ids tid=
      let cur_t = self#get_tree tid in
      let id = EntTree.get_next_id () in
      let () = Debug.ninfo_hprint (add_str  "new tree id" string_of_int) (id) no_pos in
      let nt = {cur_t with EntTree.m_tree_id = id;
          EntTree.m_node_ids = cur_t.EntTree.m_node_ids@new_node_ids
      } in
      let () = self#set_tree id nt in
      let () = m_waiting_ctrees <- m_waiting_ctrees@[id] in
      ()
    in
    let rec aux ls=
      match ls with
        | [] -> []
        | [x] -> x (* the last set will be added into the current tree *)
        | x::rest ->
              let new_node_ids = (List.map (fun n -> n.N.id) x) in
              let () = List.iter (aux_clone new_node_ids) tree_ids in
              aux rest
    in
    aux ls_new_nodes

  method do_expand cur child_ews =
    let ls_children = List.map (self#construct_child cur) child_ews in
    (* lookup all trees containing cur *)
    let tree_ids = [m_working_ctree]@(self#get_waiting_tree_contain cur.N.id) in
    let () = Debug.ninfo_hprint (add_str "tree_ids" (pr_list string_of_int)) tree_ids no_pos in
    let children = self#clone_tree tree_ids ls_children in
    let child_ids = (List.map (fun n -> n.N.id) children) in
    let () = List.iter (fun tid -> self#update_tree_nodes tid child_ids) tree_ids in
    let () = cur.N.status <- Nreduced in
    children

  method update_invalid_tree n=
     let t = self#get_tree m_working_ctree in
     let n_t = EntTree.update_tree_invalid t n.N.id in
     let () = self#set_tree m_working_ctree n_t in
     let () = m_invalid_ctrees <- m_invalid_ctrees@[t.EntTree.m_tree_id] in
     let () = Debug.ninfo_hprint (add_str  "INVALID tree" string_of_int) t.EntTree.m_tree_id no_pos in
     ()

  method build_iter bound onodes=
    if bound <= 0 then
      let () = m_termination <- false in
      Out.NONTERM
    else begin
      let invalid, cur_opt, rest, cc_leave = self#lookup_open onodes in
      match invalid with
        | Some n ->
              let () = self#update_invalid_tree n in
              Out.INVALID
        | None -> begin
            match cur_opt with
              | Some cur -> begin
                  let child_ews, is_lufold, stuck = match cc_leave with
                    | [] -> (* unfold *)
                          let child_ews,is_lufold,stuck = self#unfold cur in
                          child_ews,is_lufold, stuck
                    | leave -> [leave], false, ENorm
                  in
                  if (stuck != ENorm) then begin
                    match stuck with
                      | ELuEmp ->  let () = cur.N.status <- Nvalid in
                        self # build_iter (bound - 1) rest
                      | EBaseNoMatch ->
                            let () = cur.N.data.EntNode.ENT_NODE_DATA.stuck <- stuck in
                            let () = cur.N.status <- Ninvalid in
                            let () = self#update_invalid_tree cur in
                            Out.INVALID
                      | _  -> begin
                            let () = cur.N.data.EntNode.ENT_NODE_DATA.stuck <- stuck in
                            (* check sat *)
                            let r,_,_= EntNode.ENT_NODE_DATA.check_sat_ante m_pdecls cur.N.data m_bheap_only in
                            let () = Debug.ninfo_hprint (add_str  "Stuck: " Out.string_of) r no_pos in
                            match r with
                              | Out.SAT ->
                                    let is_abd, ass = m_abd_sat_fnc cur.N.data.EntNode.ENT_NODE_DATA.ante.SLND.arith.SLND.arith_pure in
                                    if is_abd then
                                      let () = m_assumptions <- m_assumptions@ass in
                                      let () = cur.N.status <- Nvalid in
                                      self # build_iter (bound - 1) rest
                                    else
                                    let () = cur.N.status <- Ninvalid in
                                    let () = self#update_invalid_tree cur in
                                    Out.INVALID
                              | Out.UNSAT -> let () = cur.N.status <- Nvalid in
                                self # build_iter (bound - 1) rest
                              | _ -> Out.UNKNOWN
                        end
                  end
                  else
                    let children = self#do_expand cur child_ews in
                    let () = if true(* is_lufold *) then m_reduced_nodes <- m_reduced_nodes@[cur.N.id]
                    else () in
                    let new_opens = children@rest in
                    self # build_iter (bound - 1) new_opens
                end
              | None ->
                    let () = Debug.ninfo_hprint (add_str  "No more open leaf" string_of_int) (m_bound - bound) no_pos in
                    let () = Debug.ninfo_hprint (add_str  "onodes" (pr_list_ln N.string_of)) onodes no_pos in
                    Out.VALID (*END*)
          end
    end

  method get_tree_status tree=
    let rec aux nodes=
      match nodes with
        | n_id::rest ->
              let n = self# get_node n_id in
              if n.N.status == Ninvalid then
                Out.INVALID, Some n
              else aux rest
        | [] -> Out.VALID, None
    in
    aux tree.EntTree.m_node_ids


  method build_tree_iter waiting_ctrees bound=
    if not m_termination then
      (* update waiting tree -> not term *)
      ()
    else begin
      match waiting_ctrees with
        | tree_id::rest -> begin
              let () = Debug.ninfo_hprint (add_str  "working tree" string_of_int) tree_id no_pos in
              let () =  m_working_ctree <- tree_id in
              let () =  m_waiting_ctrees <- rest in
              let tree = self#get_tree tree_id in
              let r,n_opt = self#get_tree_status tree in
              match n_opt with
                | Some n ->
                      (* invalid *)
                      let n_t = EntTree.update_tree_invalid tree n.N.id in
                      let () = self#set_tree tree_id n_t in
                      let () = m_invalid_ctrees <- m_invalid_ctrees@[tree_id] in
                      self # build_tree_iter m_waiting_ctrees bound
                  | None ->
                        let onodes = self#lookup_onodes tree_id in
                        if onodes == [] then
                          self # build_tree_iter m_waiting_ctrees bound
                        else
                          let res =  self # build_iter m_bound onodes in
                          let () = Debug.ninfo_hprint (add_str  "m_waiting_ctrees" (pr_list string_of_int)) m_waiting_ctrees no_pos in
                          if res == Out.NONTERM then () else
                            if self # is_valid_tree (tree.EntTree.m_node_ids) then () else
                              self # build_tree_iter m_waiting_ctrees bound
          end
        | [] -> ()
    end

  method build_proof ()=
    let () = EntTree.reset_cur_id () in
    let () = m_next_node_id <- init.N.id + 1 in
    (*simplify m_root?*)
    (* add root into the first of m_nodes *)
    let () = Array.set m_nodes 0 m_root in
    (* new tree *)
    let init_id = EntTree.get_next_id () in
    let init_tree = EntTree.make init_id [init.N.id] true None in
    let () = Array.set m_ctrees init_id init_tree in
    let () = m_waiting_ctrees <- [init_id] in
    let () = self # build_tree_iter m_waiting_ctrees m_bound in
    let () = Debug.ninfo_hprint (add_str  "subterm_map" (pr_list (SUBT.string_of))) m_subterm_map no_pos in
    if !VarGen.ent_show_proof then
      let () = Debug.info_hprint (add_str  "FOREST" pr_id) (self#string_of()) no_pos in
      ()
    else
      ()

  method is_valid_tree ids0=
    let rec aux ids res=
      match ids with
        | id::rest ->
              let n = Array.get m_nodes id in
              let () = Debug.ninfo_hprint (add_str  "n.N.id" (string_of_int)) id no_pos in
              let () = Debug.ninfo_hprint (add_str  "n.N.child" (pr_list string_of_int)) n.N.child no_pos in
              if n.N.child == [] then begin
                if n.N.status == Nvalid || n.N.status == Ncycle then
                  aux rest (res+1)
                else
                  let () = if !VarGen.ent_show_proof then
                    Debug.info_hprint (add_str  "leaves caused UNKNOWN" (string_of_int)) id no_pos else ()
                  in
                  (false, res)
              end
              else (* check whether incomplete condition *)
                if (Gen.BList.intersect_eq (=) n.N.child ids0) != [] then
                  aux rest res
                else (false, res)
        | [] -> true, res
    in
    let r, num_valid = aux ids0 0 in
    let () = Debug.ninfo_hprint (add_str  "ids" (pr_list string_of_int)) ids0 no_pos in
    let () = Debug.ninfo_hprint (add_str  "is valid?" string_of_bool) r no_pos in
    let () = Debug.ninfo_hprint (add_str  "num valid?" string_of_int) num_valid no_pos in
    r && (num_valid > 0)

  method lookup_valid_tree ()=
    let cur_tree_id = EntTree.get_cur_id () in
    let rec aux id res=
      if id < cur_tree_id then
        let t = Array.get m_ctrees id in
        match t.EntTree.m_invalid_node_id with
          | None -> begin
              (* all leaves are valid or cycle?*)
               let () = Debug.ninfo_hprint (add_str  "not invalid, is valid?" string_of_int) id no_pos in
              if t.EntTree.m_term && self#is_valid_tree t.EntTree.m_node_ids then
                res@[id]
              else aux (id+1) res
            end
          | Some _ -> aux (id+1) res
      else res
    in
    aux 0 []

  method string_of_all_ctree ()=
    let cur_tree_id = EntTree.get_cur_id () in
    let rec aux id=
      if id < cur_tree_id then
        let t = Array.get m_ctrees id in
        let () = Debug.info_hprint (add_str  "End:tree" EntTree.string_of) t no_pos in
        aux (id+1)
      else ()
    in aux 0

  method check_valid ()=
    (* let () = self#string_of_all_ctree () in *)
    if m_termination then
      let valid_ctrees = self # lookup_valid_tree () in
      let () = Debug.ninfo_hprint (add_str  "valid_ctrees" (pr_list string_of_int)) valid_ctrees no_pos in
      (* let () = Debug.ninfo_hprint (add_str  "invalid_ctrees" (pr_list string_of_int)) m_invalid_ctrees no_pos in *)
      (* let () = Debug.ninfo_hprint (add_str  "get_cur_id" ( string_of_int)) (EntTree.get_cur_id ()) no_pos in *)
      (* let () = Debug.ninfo_hprint (add_str  "m_waiting_ctrees" (pr_list string_of_int)) m_waiting_ctrees no_pos in *)
      match valid_ctrees with
        | t_id::_ ->
              (* valid *)
              let t = self#get_tree t_id in
              let () = if !VarGen.ent_show_proof then
                let () = Debug.info_hprint (add_str  "valid proof" EntTree.string_of) t no_pos in ()
              else () in
              Out.VALID, []
        | [] -> begin
            match m_invalid_ctrees with
              | id::_ -> if m_waiting_ctrees == [] &&
                  (List.length m_invalid_ctrees) == (EntTree.get_cur_id ()) then
                    Out.INVALID, [id]
                else Out.UNKNOWN, []
                        (* valid *)
              | [] -> Out.UNKNOWN, []
          end
    else
      (* not terminate *)
      Out.UNKNOWN, []


end;;
