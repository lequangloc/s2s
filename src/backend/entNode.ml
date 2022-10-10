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
module EQ = Eql

module SLU = SlUtil
module SLN = SlNode
module SLND = SlNode.SL_NODE_DATA

module ENT_NODE_DATA = struct

  type t = {
      ante : SLND.t;
      cons: SLND.t;
      qvars: Var.t list; (* implicit ex quantified vars *)
      fp: Cheap.t;
      mutable b_lu: bool;
      mutable stuck: entstuck;
  }


  let string_of (e: t)=
     "impl exists " ^ ((pr_list Var.string_of) e.qvars) ^ ": " ^
      ((SLND.string_of) e.ante) ^ "\n" ^
        "   |= " ^ (SLND.string_of e.cons)  ^ "\n" ^
        "footprint == " ^ (Cheap.string_of e.fp) ^ "\n" ^
        "stuck == " ^ (string_of_entstuck e.stuck) ^ "\n"


  let string_of_short (e: t)=
    let lhs = SLN.star_compose e.ante in
    let rhs = SLN.star_compose e.cons in
    "impl exists " ^ ((pr_list Var.string_of) e.qvars) ^ ": "  ^
        "hvars " ^ ((Var.string_of_list) (SLND.get_hvars e.ante)) ^ ": "  ^
        ((CF.string_of) lhs) ^ "\n" ^
        "   |= " ^ (CF.string_of rhs)  ^ "\n" ^
        "footprint == " ^ (Cheap.string_of e.fp) ^ "\n" ^
        "lu == " ^ (string_of_bool e.b_lu) ^ "\n" ^
        "stuck == " ^ (string_of_entstuck e.stuck) ^ "\n"

  let get_hvars_fp e=
    let _, cptos = CH.star_decompose e.fp in
    List.map (fun dn -> dn.CPoN.hpto_node) cptos

  let is_fp_normalized_view_contra cpreds e=
    let vns0, _ = CH.star_decompose e.fp in
    let null_vars = e.ante.SLND.heap.SLND.eql_f.EQ.null_vars in
    let diseqs = e.ante.SLND.heap.SLND.eql_f.EQ.diseqs in
    let all_contra_vs = (SLND.get_hvars e.ante)@null_vars in
    let rec fold_left_return_first vns=
      match vns with
        | vn::rest -> begin
              let srcs,ltars = Cpred.get_root_src_tar_acyclic cpreds vn.CPeN.hpred_name vn.CPeN.hpred_arguments in
              match srcs, ltars with
                | s::_,t::_ -> begin
                      (*is it normalized*)
                      if List.exists (fun (v1,v2) -> (Var.equal s v1 &&
                          Var.equal t v2) || (Var.equal s v2 &&
                          Var.equal t v1)
                      ) diseqs then
                        (*contra with ante: points-to exists*)
                        if Var.mem s all_contra_vs then
                          true
                        else fold_left_return_first rest
                      else fold_left_return_first rest
                  end
                | _ -> fold_left_return_first rest
          end
        | [] -> false
    in
    let all_vns = (vns0@e.ante.SLND.heap.SLND.hpreds) in
    if all_vns == [] then false, true, vns0
    else
      fold_left_return_first  all_vns, false, vns0

  let hypo e=
    let leql = e.ante.SLND.heap.SLND.eql_f in
    let reql = e.cons.SLND.heap.SLND.eql_f in
    let n_reql = EQ.hypo leql reql in
    let lqf_eql = e.ante.SLND.heap.SLND.qf_eql_f in
    let rqf_eql = e.cons.SLND.heap.SLND.qf_eql_f in
    let n_rqf_eql = EQ.hypo lqf_eql rqf_eql in
    let n_r_heap = {e.cons.SLND.heap with SLND.eql_f = n_reql;
        SLND.qf_eql_f = n_rqf_eql;
    } in
    (* arith *)
    (* let rhs_p = Cpure.add_quantifiers (List.filter (fun v -> not (Var.is_node v)) e.cons.SLND.qvars)  e.cons.SLND.arith.SLND.arith_pure in *)
    (* let n_ra = if Com.is_imply e.ante.SLND.arith.SLND.arith_pure *)
    (*   rhs_p then *)
    (*     { e.cons.SLND.arith with SLND.arith_pure = Cpure.mkTrue no_pos} *)
    (* else e.cons.SLND.arith *)
    (* in *)
    let n_cons = {e.cons with SLND.heap = n_r_heap;
        (* SLND.arith = n_ra; *)
    } in
    {e with cons = n_cons}

  (* Rule #null and #*: update svs nodes into e:
     - add disnull for each v in svs
     - add diseq for vi, vj in svs
     - add diseq for each vi in svs and each vi in e
  *)
  (* let update_star_new_nodes e svs= *)
  (*   let n_ante = SLND.update_star_new_nodes *)
  (*     e.ante svs in *)
  (*   {e with ante = n_ante} *)

  let elim_ex_null_var e=
    let sst1, n_ante = SLND.elim_ex_null_var e.ante in
    let sst2, n_cons = SLND.elim_ex_null_var e.cons in
    if sst1 != [] || sst2 != [] then
      let n_qvars, n_fp = if sst1 = [] then e.qvars, e.fp
      else Var.diff e.qvars (List.map fst sst1), CH.h_subst sst1 e.fp
      in
      (* add null_var into ante *)
      let n_ante1 = SLND.add_spec_null_var n_ante in
      { e with ante = n_ante1; cons = n_cons;
          qvars = n_qvars; fp = n_fp;
      }
    else e

    (* As we do not apply EX-MID for all,
           to be more complete
           we need to check LHS == UNSAT for
           the stuck node
    *)
  let check_sat_ante pdecls e heap_only=
    let cpreds, cptos = CH.star_decompose e.fp in
    let lh = e.ante.SLND.heap in
    let n_lh = {lh with SLND.hpreds = lh.SLND.hpreds@cpreds;
        SLND.hptos = lh.SLND.hptos@cptos;
    } in
    let n_ante = {e.ante with SLND.heap = n_lh} in
    SlSat.check_sat_from_data pdecls heap_only false
        true true false n_ante Com.tree_bound_sat Com.tree_size_sat

  let checksat_wrapper pdecls fnc bheap_only f0=
    let checksat_direct f=
       (* let r, _ = Kengine.check_sat pdecls f in *)
      let r, _, _ = SlSat.check_sat_from_data pdecls bheap_only false true true false f0 Com.tree_bound_sat Com.tree_size_sat in
       r
    in
    (* let rec iter_checksat fs r= *)
    (*   match fs with *)
    (*     | f2::rest -> *)
    (*           let r2 = checksat_direct f2 in *)
    (*           if r2==Out.UNSAT then iter_checksat rest r2 *)
    (*           else r2 *)
    (*     | [] -> r *)
    (* in *)
    (* let f1 = SLN.star_compose f0 in *)
    checksat_direct f0

  let check_lroot_not_match (lqvars, lvns, lptos) (rqvars, rvns, rptos)=
    let rec aux cur_ptos done_ptos=
      match cur_ptos with
        | ln::rest -> begin
            if List.exists (fun ln1 -> Var.equal ln.CPoN.hpto_node ln1.CPoN.hpto_node) rest then
              raise LPTO_DUPS_EXC
            else
              if List.exists (fun ln1 -> Var.mem ln.CPoN.hpto_node ln1.CPoN.hpto_arguments) (rest@done_ptos) ||
                List.exists (fun vn -> Var.mem ln.CPoN.hpto_node vn.CPeN.hpred_arguments) lvns
              then
                (*not root*)
                aux rest (done_ptos@[ln])
              else
                (*root. compare againt rhs*)
                if (List.for_all (fun rn -> not (Var.equal ln.CPoN.hpto_node rn.CPoN.hpto_node)
                    ) rptos) &&
                    (List.for_all (fun rv -> not (Var.mem ln.CPoN.hpto_node rv.CPeN.hpred_arguments)
                    ) rvns) then true
                else aux rest (done_ptos@[ln])
            end
        | [] -> false
    in
    try
      if aux lptos [] then Out.INVALID
      else
        Out.UNKNOWN
    with LPTO_DUPS_EXC -> Out.VALID

        (*fix cyclic for linear, then remove this function*)
  let temp_invalid_check  pdecls bheap_only  lhs reql=
    if reql.EQ.qvars ==[] && reql.EQ.eqs==[] &&
      reql.EQ.null_vars==[] && reql.EQ.disnull_vars==[] then
        match reql.EQ.diseqs with
          | [a] -> (* lhs /\ not reql *)
                let h = lhs.SLND.heap in
            let eql = h.SLND.eql_f in
            let n_eql = {eql with EQ.eqs = eql.EQ.eqs@reql.EQ.diseqs} in
            let n_h = {h with SLND.eql_f = n_eql} in
            let ncom_lhs = {lhs with SLND.heap = n_h} in
            let ra, _, _ = SlSat.check_sat_from_data pdecls bheap_only false
              true true false ncom_lhs Com.tree_bound_sat Com.tree_size_sat in
            if ra == Out.UNSAT then true
            else false
          | _ -> false
    else false

        (*over-approxiamtedly checking validity
          for heap only entailment*)
  let eval_ho pdecls bheap_only e=
    let e_lhs = e.ante in
    let e_rhs = e.cons in
    let lqvars, lvns, lptos, leql, _ = SLN.star_decompose e_lhs in
    let rqvars, rvns, rptos, reql0, _ = SLN.star_decompose e_rhs in
    (* let fp = CF.mkBase e.fp (CP.mkTrue no_pos) no_pos in *)
    (*quick check first*)
    let r, _ = SLND.eval pdecls bheap_only [] e_lhs in
    if r == Out.UNSAT then
       Out.VALID
    else
      if (rvns ==[] && rptos ==[]) || (EQ.check_sat_over reql0 ==Out.UNSAT)  then
        let _, _, reql = EQ.elim_ex_null_var reql0 in
        (* let reql = EQ.hypo leql reql1 in *)
        if lvns ==[] && lptos ==[] then
          (* reql == top => VALID*)
          (* let _,_,sst,leql1 = EQ.elim_eq leql in *)
          (* let reql = if sst == [] then reql else EQ.subst sst reql in *)
          (* let reql = EQ.hypo leql1 reql in *)
          if (EQ.is_top reql) then
            Out.VALID
          else
            (* let _, com_ante = SLN.mkStarAnd_f pdecls true e_lhs fp in *)
            let fp_views, _ = CH.star_decompose e.fp in
            let com_ante = {e_lhs with SLND.heap = {e_lhs.SLND.heap with hpreds = e_lhs.SLND.heap.hpreds@fp_views}} in
            let ra, _, _ = SlSat.check_sat_from_data pdecls bheap_only false
              true true false com_ante Com.tree_bound_sat Com.tree_size_sat in
            if ra == Out.UNSAT then Out.VALID
            else
              (* let com_cons = SLN.mkStarAnd com_ante e_rhs in *)
              (* let rb, _, _ = SlSat.check_sat_from_data pdecls bheap_only false *)
              (*   true true false com_cons Com.tree_bound_sat in *)
              (* if rb == Out.UNSAT then Out.INVALID else *)
              (*   Out.UNKNOWN *)
              if temp_invalid_check pdecls bheap_only com_ante reql
              then VALID else
                Out.INVALID
        else (* LHS heap != emp /\ RHS heap = emp *)
          if lptos != [] then
            let is_contra, is_invalid, fp_vns = is_fp_normalized_view_contra pdecls e in
            if is_invalid then Out.INVALID else
              if is_contra then Out.VALID  else
                (* let _, com_ante = SLN.mkStarAnd_f pdecls true e_lhs fp in *)
                let com_ante = {e_lhs with SLND.heap = {e_lhs.SLND.heap with hpreds = e_lhs.SLND.heap.hpreds@fp_vns}} in
                let ra, _, _ = SlSat.check_sat_from_data pdecls bheap_only false
                  true true false com_ante Com.tree_bound_sat Com.tree_size_sat in
                if ra == Out.UNSAT then Out.VALID
                else
                  Out.INVALID
          else
            Out.UNKNOWN
      else (* RHS heap != emp *)
        (* if lvns ==[] && lptos ==[] then (\* LHS heap == emp /\ RHS heap != emp *\) *)
        if lvns ==[] && lptos ==[] && rptos !=[] (* ((List.length rptos) > (List.length lptos)) *) then
          let _, com_ante = SLN.mkStarAnd_f pdecls true e_lhs (CF.mkBase e.fp (CP.mkTrue no_pos) no_pos) in
          let ra, _, _ = SlSat.check_sat_from_data pdecls bheap_only false 
            true true false com_ante Com.tree_bound_sat Com.tree_size_sat in
          if ra == Out.UNSAT then Out.VALID  else
            Out.INVALID
        else
        Out.UNKNOWN

  let eval pdecls bheap_only cur_ass  e=
    let () = Debug.ninfo_hprint (add_str  "ent_tree.eval" string_of) e no_pos in
    let () = Debug.ninfo_hprint (add_str  "(ENT)bheap_only" string_of_bool) bheap_only no_pos in
     if bheap_only then
       let r = eval_ho pdecls bheap_only e in
       r, []
     else
        let sat_fnc = SLND.eval_all bheap_only in
        let e_lhs = e.ante in
        let e_rhs = e.cons in
        let fp = CF.mkBase e.fp (CP.mkTrue no_pos) no_pos in
        (* empty heap in both side *)
        let lqvars, lvns, lptos, leql, la = SLN.star_decompose e_lhs in
        let rqvars, rvns, rptos, reql, ra = SLN.star_decompose e_rhs in
        let lp = SLND.to_pure e_lhs in
        let rp = CP.mkAnd (EQ.to_pure e_rhs.SLND.heap.SLND.eql_f)
          e_rhs.SLND.arith.SLND.arith_pure no_pos
        in
        let r2, _ = SLND.eval pdecls bheap_only [] e_lhs in
        if r2 == Out.UNSAT then
          Out.VALID, []
        else
          let rhs_pure_res = EQ.check_sat_over reql in
          if (rvns ==[] && rptos ==[]) || (rhs_pure_res ==Out.UNSAT) then
            if lvns ==[] && lptos ==[] then
              if CP.isTrue rp then Out.VALID, [] else
              let rhs_p =
                let p_rqvars = Var.intersect rqvars (CP.fv rp) in
                if p_rqvars = [] then rp else
                  CP.add_quantifiers p_rqvars rp
              in
              let fb_or_bases = CfUtil.unfold_base_pair pdecls false fp in
              let p_or_fp_bases = List.map (fun fp_base ->
                  let e_fp= SlNode.mk_data pdecls false fp_base in
                  let p_fp = CP.mkAnd (CP.mkAnd (EQ.to_pure e_fp.SLND.heap.SLND.eql_f) e_fp.SLND.arith.SLND.arith_pure no_pos)  e_fp.SLND.arith.SLND.inv_preds no_pos in
                  p_fp
              ) fb_or_bases in
              let p_fp_base = CP.join_disjunctions p_or_fp_bases in
              let () = Debug.ninfo_hprint (add_str  "p_fp_base" (CP.string_of)) p_fp_base no_pos in
              let ante0 =  (CP.mkAnd lp p_fp_base no_pos) in
              let p_lqvars = Var.intersect lqvars (CP.fv lp) in
              let ante1 = if p_lqvars = [] then ante0 else CP.add_quantifiers p_lqvars ante0 in
              let () = Debug.ninfo_hprint (add_str  "ante1" (CP.string_of)) ante1 no_pos in
              (* let rhs_p1 = CP.eql_simplify rhs_p in *)
              let () = Debug.ninfo_hprint (add_str  "rhs_p" (CP.string_of)) rhs_p no_pos in
              (* let () = Debug.ninfo_hprint (add_str  "rhs_p1" (CP.string_of)) rhs_p1 no_pos in *)
              (* let r = Com.is_imply ante1 rhs_p in *)
              let r, ass = Abd.arith_abduce cur_ass ante1 rhs_p in
              let () = Debug.ninfo_hprint (add_str  "ante1 |- rhs_p" (string_of_bool)) r no_pos in
              if r then Out.VALID, ass else Out.INVALID, ass
            else
              (* LHS contains a pto or pred that is not in RHS ==> invalid*)
              (* let r = check_lroot_not_match (lqvars, lvns, lptos) (rqvars, rvns, rptos) in *)
              (* if r != Out.UNKNOWN then r *)
              (* else *)
              (* LHS is unsat -> valid *)
              let _, comb_ante = SLN.mkStarAnd_f pdecls true e_lhs fp (* if b_heap_only then (SLN.mkStarAnd_f pdecls true e_lhs fp) else *) in
              let () = Debug.ninfo_hprint (add_str  "comb_ante: " (SLND.string_of)) comb_ante no_pos in
              (* let r2, _ = Kengine.check_sat pdecls comb_ante in *)
              let r2 = checksat_wrapper pdecls sat_fnc bheap_only comb_ante in
              let () = Debug.ninfo_hprint (add_str  "comb_ante out: " (Out.string_of)) r2 no_pos in
              if r2 == Out.UNSAT then Out.VALID, []
              else if r2 == Out.SAT then
                (* RHS is unsat -> invalid *)
                (* let _, rhs_cmd = SLN.mkStarAnd_f pdecls true e_rhs fp (\* (CF.mkStarAnd e_rhs fp) *\) in *)
                (* let r3 = checksat_wrapper pdecls sat_fnc bheap_only rhs_cmd in *)
                (* let () = Debug.info_hprint (add_str  "rhs_cmd out: " (Out.string_of)) r3 no_pos in *)
                if rhs_pure_res == Out.UNSAT then Out.INVALID, []
                else
                  begin
                    (* if ((SLND.is_empty_heap_or_htrue e_lhs) *)
                    (* && lvns==[] && lptos ==[] && rptos !=[]) || *)
                    (*   ((SLND.is_empty_heap_or_htrue e_rhs ) *)
                    (*   && lptos !=[] && rptos ==[] && rvns==[] ) *)
                    (* then Out.INVALID *)
                    (* else *)
                      let leqNulls, _, leqs, _ =  EQ.decompose leql in
                      let l_nulls = Var.get_eq_closure leqs leqNulls in
                      let l_allocas = Var.get_eq_closure leqs (List.map (fun n -> n.CPoN.hpto_node) lptos) in
                      let reqNulls, _, reqs, _ =   EQ.decompose reql in
                      let r_nulls = Var.get_eq_closure reqs reqNulls in
                      let r_allocas = Var.get_eq_closure reqs (List.map (fun n -> n.CPoN.hpto_node) rptos) in
                      if (Var.intersect l_nulls r_allocas != []) ||
                        (Var.intersect r_nulls l_allocas != [])
                      then Out.INVALID, [] else
                        Out.UNKNOWN, []
                  end
              else Out.UNKNOWN, []
          else
            Out.UNKNOWN, []

 let eval_all _ e=
   Out.UNKNOWN

end;;

open ENT_NODE_DATA

let make_cons impl_vars ln rn fp=
  let e = {
      ante = ln;
      cons = rn;
      qvars = impl_vars;
      fp =  fp;
      b_lu = false;
      stuck = ENorm;
  } in hypo e

let make_x pdecls impl_vars a c fp =
  let e= {
      ante = SLN.mk_data pdecls false (snd (CF.remove_redundant a));
      cons = SLN.mk_data pdecls false (snd (CF.remove_redundant c));
      qvars = impl_vars; (* impl qvars;*)
      fp =  fp;
      b_lu = false;
      stuck = ENorm;
  } in hypo e

let make pdecls impl_vars a c fp =
  let pr1 = CF.string_of in
  let pr2 = CH.string_of in
  Debug.no_4 "EntNode.make" Var.string_of_list pr1 pr1 pr2 string_of
      (fun _ _ _ _ -> make_x pdecls impl_vars a c fp)
      impl_vars a c fp

let get_univ_ptos qvars eqs ptos=
  let univ_ptos, vars = List.fold_left (fun (r1, r2) n ->
      let l_cl = Var.get_eq_closure eqs [n.CPoN.hpto_node] in
      if (Var.diff l_cl qvars != []) then (r1@[n], r2@[n.CPoN.hpto_node])
      else (r1, r2)
  ) ([],[]) ptos in
  univ_ptos, vars

let get_univ_preds qvars eqs views=
  let univ_views = List.filter (fun n ->
      let l_cl = Var.get_eq_closure eqs n.CPeN.hpred_arguments in
      Var.diff l_cl qvars != []
  ) views  in
  univ_views

module ENTNODE = Node.FNode(ENT_NODE_DATA)

