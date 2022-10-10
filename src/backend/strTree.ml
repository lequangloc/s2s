open Globals
open Gen
open VarGen

open Com

module ENTRY = StrNode.STR_NODE_DATA
module N = StrNode.STRNODE
module E = StrEdge.STREDGE

module BL = E

module STR_SUBTERM_ELT = struct
  type t = Var.t
  let string_of = Var.string_of

  let equal = Var.equal

end;;

module SUBT = Subterm.FSubTerm(STR_SUBTERM_ELT)

class ['t] cyclic init b = object(self)
  val mutable m_root: 't = init
  val mutable m_next_id = 1
  val m_bound = b
  val mutable m_nodes: 't array = Array.make tree_size_sat init
  val mutable m_edges : E.t list = []
  val mutable m_back_links:  BL.t list = []


  val mutable m_leaves: 't list = []
  val mutable m_termination: bool = true

 (* for back-link construction *)
  val mutable m_subterm_map: SUBT.t list = []
    (* companion candidates*)
  val mutable m_reduced_nodes: int list = []

  (* eval a node and set its status accordingly *)
  method eval (e: 't) =
    let o = N.eval [] false e in
    if o = Out.SAT || o == Out.UNSAT then true
    else false

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

  method update_subterm sv sub_sv=
    let rec lookup_and_insert sv ls sub_done=
      match ls with
        | [] -> false, sub_done
        | xs::sub_rest ->
              if SUBT.mem sv xs then
                let up_subterm = SUBT.append xs [sub_sv] in
                true, sub_done@[(up_subterm)]@sub_rest
              else lookup_and_insert sv sub_rest (sub_done@[xs])
    in
    let res, ls = lookup_and_insert sv m_subterm_map [] in
    let new_map = if res then ls
    else ls@[(SUBT.mk [sv;sub_sv])]
    in
    m_subterm_map <- new_map

  method link_back n=
    let () = Debug.ninfo_hprint (add_str  "link_back (input)"
    N.string_of) n no_pos in
    let bud_svs = Var.remove_dups (Term.fv n.N.data.ENTRY.ew) in
    let rec lookup_subterm_rel bud_sv comp_svs done_comp=
      match comp_svs with
        | [] -> None, done_comp
        | sv::rest ->
              if List.exists (fun svl ->
                  (Gen.BList.difference_eq Var.equal [bud_sv;sv] svl) == []
              ) m_subterm_map then
                Some (bud_sv, Exp.mkVar sv no_pos), done_comp@rest
              else lookup_subterm_rel bud_sv rest (done_comp@[sv])
    in
    let rec do_link ls=
      match ls with
        | [] -> false
        | id::rest ->
              let comp = Array.get m_nodes id in
              let () = Debug.ninfo_hprint (add_str  "link_back (comp)"
 (N.string_of)) comp no_pos in
              let comp_svs = Var.remove_dups (Term.fv comp.N.data.ENTRY.ew) in
              let inter_svs = Var.remove_dups  (Gen.BList.intersect_eq Var.equal bud_svs comp_svs) in
              let bud_diff = Var.remove_dups  (Gen.BList.difference_eq Var.equal bud_svs inter_svs) in
              let () = Debug.ninfo_hprint (add_str  "link_back (bud_diff)"
 (pr_list Var.string_of)) (bud_diff) no_pos in
              let comp_diff = Var.remove_dups  (Gen.BList.difference_eq Var.equal comp_svs inter_svs) in
              let () = Debug.ninfo_hprint (add_str  "link_back (comp_diff)"
 (pr_list Var.string_of)) (comp_diff) no_pos in
              if (List.length bud_diff) != (List.length comp_diff) then do_link rest
              else
                begin try
                  let sst,_ = List.fold_left (fun (sst0, comp_svs) bud_sv ->
                      let res, rest_comp_svs =
                        lookup_subterm_rel bud_sv comp_svs [] in
                      match res with
                        | Some ss -> (sst0@[ss], rest_comp_svs)
                        | None -> raise Not_found
                  ) ([], comp_diff) bud_diff in
                  (* identical, do not process, but not cycle *)
                  (* if sst == [] then do_link rest else *)
                    let substed_bud = Term.t_subst sst n.N.data.ENTRY.ew in
                    if Term.equalTerm Var.equal substed_bud comp.N.data.ENTRY.ew then
                      (* add a back link*)
                      let back_link = {E.from_id = n.N.id;
                      E.to_id = id;
                      E.label = sst;
                      } in
                      let () = n.N.status <- Ncycle in
                      let () = m_back_links <- m_back_links@[back_link] in
                      true
                    else do_link rest
                with Not_found -> do_link rest
                end
    in
    let res= if n.N.parent == root_parent_ID then false (* root *)
    else
      do_link m_reduced_nodes
    in
    let () = Debug.ninfo_hprint (add_str  "link_back (output)"
 (string_of_bool)) res no_pos in
    res

  method matching ((ew): Term.t ) : Term.t =
    let rec helper lhs rhs p=
      match lhs, rhs with
        | [],[] -> let semp = Exp.mkEmpCConst p in
          Term.Eq (semp, semp, p)
        | [], y::rrest -> let n_lhs = Exp.mkEmpCConst p in
          let n_rhs = Exp.combine_concat y rrest p in
          Term.Eq (n_lhs, n_rhs, p)
        | x::lrest, [] -> let n_lhs = Exp.combine_concat x lrest p in
          let n_rhs = Exp.mkEmpCConst p in
          Term.Eq (n_lhs, n_rhs, p)
        | x::lrest, y::rrest -> begin
            if Exp.eqExp_f Var.equal x y then
              helper lrest rrest p
            else
              let n_lhs = Exp.combine_concat x lrest p in
              let n_rhs = Exp.combine_concat y rrest p in
              Term.Eq (n_lhs, n_rhs, p)
          end
    in
    let new_ew = match ew with
      | Term.Eq (e1, e2, p) -> begin
          let ts_lhs = Exp.flatten_concat e1 [] in
          let ts_rhs = Exp.flatten_concat e2 [] in
          helper ts_lhs ts_rhs p
        end
      | _ -> ew
    in
    (new_ew)

  method complete_aux_var_char ew sv c pos is_only_heads =
    let semp = Exp.mkEmpCConst pos in
    if not is_only_heads then
      let ew1 = Term.t_subst_one_term (sv, semp) ew in
      let () = Debug.ninfo_hprint (add_str  "ew1" (Term.string_of)) ew1 no_pos in
      let fr_sv = Var.fresh_var sv in
      let e = Exp.mkConcatExp (Exp.mkCConst c pos)
        (Exp.mkVar fr_sv pos) pos in
      let () = Debug.ninfo_hprint (add_str  "e" (Exp.string_of)) e no_pos in
      let ew2 = Term.t_subst_one_term (sv, e) ew in
      let () = self # update_subterm sv fr_sv in
      let () = Debug.ninfo_hprint (add_str  "ew2" (Term.string_of)) ew2 no_pos in
      [(ew1, (sv, semp));(ew2, (sv, e))]
    else
      let ew3 = Term.mkEq semp semp pos in
      [(ew3, (sv, (Exp.mkCConst c pos)))]

  method complete_aux_var_var ew sv1 sv2 pos is_only_heads =
    let () = Debug.ninfo_hprint (add_str  "complete_aux_var_var. input"
        (pr_id)) "tbd" no_pos in
    let semp = Exp.mkEmpCConst pos in
    if not is_only_heads then
      let ew1 = Term.t_subst_one_term (sv1, semp) ew in
      let fr_sv1 = Var.fresh_var sv1 in
      let e1 = Exp.mkConcatExp (Exp.mkVar sv2 pos)
        (Exp.mkVar fr_sv1 pos) pos in
      let () = Debug.ninfo_hprint (add_str  "e1" (Exp.string_of)) e1 no_pos in
      let ew2 = Term.t_subst_one_term (sv1, e1) ew in
      let () = self # update_subterm sv1 fr_sv1 in

      let ew3 = Term.t_subst_one_term (sv2, semp) ew in
      let fr_sv2 = Var.fresh_var sv2 in
      let e2 = Exp.mkConcatExp (Exp.mkVar sv1 pos)
        (Exp.mkVar fr_sv2 pos) pos in
      let () = Debug.ninfo_hprint (add_str  "e2" (Exp.string_of)) e2 no_pos in
      let ew4 = Term.t_subst_one_term (sv2, e2) ew in
      let () = self # update_subterm sv2 fr_sv2 in
      [(ew1, (sv1, semp)); (ew2, (sv1, e1)); (ew3, (sv2, semp)); (ew4, (sv2, e2)) ]
    else
      let ew5 = Term.mkEq semp semp pos in
      [(ew5, (sv1, (Exp.mkVar sv2 pos)))]

  method complete (e: ENTRY.t)=
    let () = Debug.ninfo_hprint (add_str  "tree.complete.input" (ENTRY.string_of_short)) e no_pos in
    let head_l, head_r, is_only_heads = match e.ENTRY.ew with
      | Term.Eq (e1, e2, p) -> begin
          let hd_l = Term.head_of_string e1 in
          let hd_r = Term.head_of_string e2 in
         match hd_l, hd_r with
           | Some s1, Some s2 -> s1, s2,
                 (Term.is_only_head e1 && Term.is_only_head e2)
           | _ -> raise (Invalid_argument "tree.complete 1")
        end
      | _ -> raise (Invalid_argument "tree.complete 2")
    in
    let out = match head_l with
      | Exp.Var (sv1, p1) -> begin
          match head_r with
            | Exp.CConst (c2, _) ->
                  let ews = self#complete_aux_var_char e.ENTRY.ew sv1 c2 p1
                  is_only_heads in
                  ews
            | Exp.Var (sv2, p2) -> let ews = self#complete_aux_var_var e.ENTRY.ew sv1 sv2 p1 is_only_heads in
                  ews
            | _ -> raise (Invalid_argument "tree.complete 3")
        end
      | Exp.CConst (c1, _) -> begin
          match head_r with
            | Exp.Var (sv2, p2) ->
                  let ews = self#complete_aux_var_char e.ENTRY.ew sv2 c1 p2
                  is_only_heads in
                  ews
            | Exp.CConst (c2, _) -> raise (Invalid_argument "tree.complete 5")
            | _ -> raise (Invalid_argument "tree.complete 3")
        end
      | _ -> raise (Invalid_argument "tree.complete 4")
    in
    let () = Debug.ninfo_hprint (add_str  "tree.complete.out"
 (pr_list (pr_pair Term.string_of (pr_pair Var.string_of Exp.string_of)))) out no_pos in
    out

  method construct_child parent ews=
    let children = List.map (fun (ew, subs) ->
        let data = { ENTRY.ew = ew;
        ENTRY.ew_done = parent.N.data.ENTRY.ew_done;
        ENTRY.ew_wait = parent.N.data.ENTRY.ew_wait;
        ENTRY.re = parent.N.data.ENTRY.re;
        ENTRY.arith = parent.N.data.ENTRY.arith;
        ENTRY.inv_arith = Cpure.mk_string_inv (Cpure.BForm ew);
        ENTRY.model = [];
        } in
        let id = m_next_id in
        let () = m_next_id <- m_next_id + 1 in
        let child = { N.id = id;
        N.data = data;
        N.parent = parent.N.id;
        N.child = [];
        N.height = parent.N.height + 1;
        N.status = Nopen;
        } in
        let new_edge = { E.from_id = parent.N.id;
        E.to_id = id ;
        E.label = [subs];} in
        let () = m_edges <- m_edges @[new_edge] in
        (* update parent *)
        let () = parent.N.child <- parent.N.child @ [id] in
        (* update global data *)
        let () = Array.set m_nodes id child in
        child
    ) ews in
    children

  method unfold (e: 't)=
    let () = Debug.ninfo_hprint (add_str  "tree.unfold.input" N.string_of) e no_pos in

    let child_ews = self#complete e.N.data in
    let child_ews1 = List.map (fun (ew, subst) ->
        (self#matching ew, subst)) child_ews in

    let () = Debug.ninfo_hprint (add_str  "child_ews1 (after match)" (pr_list (pr_pair Term.string_of (pr_pair Var.string_of Exp.string_of)))) child_ews1 no_pos in
    child_ews1

  method lookup_open ls=
    match ls with
        | [] -> (None, [])
        | cur::tl -> begin
            (* eval *)
            let is_trivial = self#eval cur in
            if is_trivial then
              (* move to next *)
              self#lookup_open tl
            else if self#link_back cur then
              self#lookup_open tl
            else (Some cur, tl)
          end

  method build_iter bound onodes=
    if bound <= 0 then
      let () = m_termination <- false in
      ()
    else
      let cur_opt, rest = self#lookup_open onodes in
      match cur_opt with
        | Some cur ->
              (* back link *)
              (* unfold *)
              let child_ews = self#unfold cur in
              let children = self#construct_child cur child_ews in
              let () = cur.N.status <- Nreduced in
              let () = m_reduced_nodes <- m_reduced_nodes@[cur.N.id] in
              let new_opens = rest @ children in
              self # build_iter (bound - 1) new_opens
        | None ->
              let () = Debug.ninfo_hprint (add_str  "No more open leaf" string_of_int) bound no_pos in
              () (*END*)

  method build_proof ()=
    let () = m_next_id <- init.N.id + 1 in
    let root_ew = self#matching m_root.N.data.ENTRY.ew in
    let new_root_data = {m_root.N.data with ENTRY.ew = root_ew} in
    let () = m_root <- {m_root with N.data = new_root_data} in
    let () = Array.set m_nodes 0 m_root in
    let () =  self # build_iter m_bound [m_root] in
    let () = Debug.ninfo_hprint (add_str  "subterm_map" (pr_list (SUBT.string_of))) m_subterm_map no_pos in
    ()

   method find_satisfiability ()=
    let rec lookup_leaf id res=
      if id < m_next_id then
        let n = Array.get m_nodes id in
        if n.N.child == [] then
          lookup_leaf (id+1) (res@[id])
        else lookup_leaf (id+1) res
      else res
    in
    let leaves = lookup_leaf 0 [] in
    let sat_leaves = List.fold_left (fun r id ->
        let n =  Array.get m_nodes id in
        if (n.N.status == Nsat) then
          r@[id]
        else r
    ) [] leaves in
    if not m_termination then (Out.UNKNOWN, sat_leaves) else
      (* sat *)
      if sat_leaves != [] then
        (Out.SAT, sat_leaves)
      else if List.for_all (fun id ->
          let n =  Array.get m_nodes id in
          (n.N.status == Nunsat) || (n.N.status == Ncycle)
      ) leaves then
        (Out.UNSAT, [])
      else (Out.UNKNOWN, sat_leaves)

  (* trace from a satisfiable leaf node to the root*)
   method build_non_cycle_trace (id: int)=
     let rec bottomup_expand id (res1, res2, res3)=
       let n = Array.get m_nodes id in
       let parent_id = n.N.parent in
       if parent_id <= root_parent_ID then
         (* get vars of root *)
         let svs = Var.remove_dups
           (Term.fv n.N.data.ENTRY.ew) in
         let () = Debug.ninfo_hprint(add_str "\n build_non_cycle_trace.
root ew:\n" (Term.string_of)) n.N.data.ENTRY.ew no_pos in
         let () = Debug.ninfo_hprint(add_str "\n build_non_cycle_trace.
root svs:\n" (pr_list  Var.string_of)) svs no_pos in

         (List.rev res1, List.rev res2, Var.remove_dups (svs@res3))
       else
         let e = E.search m_edges parent_id id in
         let new_svs = List.fold_left (fun r (_, e) ->
             r @ (Exp.fv e)
         ) [] e.E.label in
         bottomup_expand parent_id (res1@[parent_id], res2@[e],
         (res3@new_svs))
     in
     bottomup_expand id ([id],[], [])

  method build_one_cycle_traces back_link=
    (* let rec is_found id_bud nexts= *)
    (*   match nexts with *)
    (*     | [] -> None *)
    (*     | (id1, e1)::rest -> if id1 = id_bud then *)
    (*         Some (id1, e1) *)
    (*       else is_found id_bud rest *)
    (* in *)
    (* let rec expand_bfs id_bud cur_traces done_traces= *)
    (*   match cur_traces with *)
    (*     | [] -> (\* next round*\) *)
    (*           expand_bfs id_bud done_traces [] *)
    (*     | (ids,tedges):: rest -> begin *)
    (*         match ids with *)
    (*           | id::_ -> begin *)
    (*                 let nexts = E.next m_edges id in *)
    (*                 let found_opt = is_found id_bud nexts in *)
    (*                 match found_opt with *)
    (*                   | None -> let new_traces = List.fold_left (fun r (n_id, n_e) -> *)
    (*                         let n = (n_id::ids, n_e::tedges) in *)
    (*                         r@[n] *)
    (*                     ) [] nexts in *)
    (*                     expand_bfs id_bud rest (done_traces@new_traces) *)
    (*                   | Some (n_id, e) -> *)
    (*                         (\* found *\) *)
    (*                         ((List.rev ids)@[n_id], (List.rev tedges)@[e]) *)
    (*             end *)
    (*           | [] -> raise (Invalid_argument "tree.build_one_cycle_traces.never_happen") *)
    (*       end *)
    (* in *)
    (* (back_link, expand_bfs back_link.E.from_id [([back_link.E.to_id],[])] []) *)
    (* travel backward from bud to companion*)
    let rec bottomup_expand id_comp id res_ids res_edges=
      let n = Array.get m_nodes id in
      let parent_id = n.N.parent in
      let res1 = res_ids@[parent_id] in
      let e = E.search m_edges parent_id id in
      let res2 = res_edges@[e] in
      if parent_id == id_comp then
        (List.rev res1, List.rev res2)
      else bottomup_expand id_comp parent_id res1 res2
    in
    let () = Debug.ninfo_hprint(add_str "\nBuild Cycle Traces:\n"  (E.string_of))
      back_link no_pos in
    (back_link, bottomup_expand back_link.E.to_id back_link.E.from_id
        [back_link.E.from_id] [])

 (* labels of cycles *)
  method build_cycle_traces ()=
    List.fold_left (fun r c ->
        try
          let new_c = self#build_one_cycle_traces c in
          r@[new_c]
        with Not_found ->
            (*identical without cycle*)
            r
    ) [] m_back_links


end;;
