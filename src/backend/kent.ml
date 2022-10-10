open Globals
open VarGen
open Gen.Basic

module CF = Cformula
module CSH = Csymheap
module CP= Cpure

open Com

module F = EntForest
module E = EntEdge
module N = EntNode.ENTNODE

(*
 - extract arith contraint on LHS (between mutpli view)
 - generate unknown pred
 - check ent and generate assumptions
 - check valid assumptions
*)

let generate_unk_pred_ante arith=
  (* if not (CP.contain_const arith) then (arith, []) else *)
  let args = Var.remove_dups (CP.fv arith) in
  if args != [] then
    let q_pred = (fresh_any_name "S") in
    let nrel = CP.BForm (Term.mkRel q_pred args no_pos) in
    let () =  Z3.add_relation q_pred args nrel in
    (* let ps = CP.split_conjunctions arith in *)
    (* let ps1 = List.filter (fun p1 -> not (CP.equal p1 arith)) ps in *)
    (* let p2 = CP.join_conjunctions (ps1@[nrel]) no_pos in *)
    nrel, [(arith, nrel)]
  else (arith, [])

let generate_unk_pred_x e=
  let _, vns, _, p = CF.decompose e.Ccmd.ante in
  let () = Debug.ninfo_hprint (add_str  "p" (CP.string_of)) p no_pos in
  let _,_,_,_, arith = CP.type_decomp p in
  let () = Debug.ninfo_hprint (add_str  "arith" (CP.string_of)) arith no_pos in
  let np, ass = generate_unk_pred_ante arith  in
  let na = match e.Ccmd.ante with
      | CF.Base fb -> let na = CF.Base {fb with CSH.base_pure = np (*p2*)} in
        na
      | CF.Exists (fb, vs) -> let na =  CF.Exists ({fb with CSH.base_pure = np (* p2 *)}, vs) in
       na
      | _ -> (e.Ccmd.ante)
  in
  {e with Ccmd.ante = na}, ass

let generate_unk_pred e=
  let pr1 = Ccmd.string_of_cmd_ent in
  let pr2 = pr_list_ln (pr_pair CP.string_of CP.string_of) in
  let pr_out = (pr_pair pr1 pr2) in
  Debug.no_1 "generate_unk_pred" pr1 pr_out
      (fun _ -> generate_unk_pred_x e) e

let generate_unk_pred_from_data_x e=
  let narith, ass = generate_unk_pred_ante e.EntNode.ENT_NODE_DATA.ante.SlNode.SL_NODE_DATA.arith.SlNode.SL_NODE_DATA.arith_pure in
  let na = {e.EntNode.ENT_NODE_DATA.ante.SlNode.SL_NODE_DATA.arith with SlNode.SL_NODE_DATA.arith_pure = narith} in
  let nante = {e.EntNode.ENT_NODE_DATA.ante with SlNode.SL_NODE_DATA.arith = na} in
  {e with EntNode.ENT_NODE_DATA.ante = nante}, ass

let generate_unk_pred_from_data e=
  let pr1 = EntNode.ENT_NODE_DATA.string_of_short in
  let pr2 = pr_list_ln (pr_pair CP.string_of CP.string_of) in
  let pr_out = (pr_pair pr1 pr2) in
  Debug.no_1 "generate_unk_pred_from_data" pr1 pr_out
      (fun _ -> generate_unk_pred_from_data_x e) e

let check_ent_gen pdecls is_heap_only is_base_reuse is_linear is_deci (e :Ccmd.cmd_ent) =
  (* let opt_abd = generate_unk_pred e in *)
  (* let e, ass = match opt_abd with *)
  (*   | None -> e, [] *)
  (*   | Some (nent, ass) -> nent, [ass] *)
  (* in *)
  if not is_heap_only && List.length pdecls > 1 then Out.VALID, None else
  let root_data = EntNode.make pdecls [] e.Ccmd.ante e.Ccmd.cons Cheap.HEmp in
  let is_rhs_ho = SlNode.SL_NODE_DATA.is_heap_only root_data.EntNode.ENT_NODE_DATA.cons in
  let rhs_eqf = root_data.EntNode.ENT_NODE_DATA.cons.SlNode.SL_NODE_DATA.heap.SlNode.SL_NODE_DATA.eql_f in
  let is_rhs_quantified_ent = List.exists (fun v -> not (Var.mem v rhs_eqf.Eql.null_vars)) root_data.EntNode.ENT_NODE_DATA.cons.SlNode.SL_NODE_DATA.qvars in
  let is_all_ho = (is_heap_only && SlNode.SL_NODE_DATA.is_heap_only root_data.EntNode.ENT_NODE_DATA.ante &&
        is_rhs_ho) in
  let () = Debug.ninfo_hprint (add_str  "is_rhs_quantified_ent" (string_of_bool)) is_rhs_quantified_ent no_pos in
  let () = Debug.ninfo_hprint (add_str  "is_all_ho" (string_of_bool)) is_all_ho no_pos in
  (* let root_data = EntNode.ENT_NODE_DATA.elim_ex_null_var root_data0 in *)
  let is_arith_ex =  not is_all_ho &&  is_rhs_quantified_ent in
  let root_data, rel_ass = if is_arith_ex then generate_unk_pred_from_data root_data
  else root_data, [] in
  let root = N.mk (root_parent_ID+1) root_data root_parent_ID
    [] 0 Nopen in
  let forest =  new F.cyclic_forest pdecls root rel_ass (!VarGen.ent_ps_colid || (is_linear))
    is_all_ho is_rhs_quantified_ent is_base_reuse
    is_deci tree_bound in
  try
    let () = forest # build_proof () in
    let r, cex = forest # check_valid () in
    let n_r = if r == Out.INVALID && is_arith_ex then
        let () = print_endline_quiet ("\nENT (INVALID -> UNK)") in
        Out.UNKNOWN
    else r
    in
    n_r, None
  with e -> begin
    let () = print_endline_quiet ("\nSLENT: exception") in
    match e with
      | Invalid_argument s ->
            let () = print_endline_quiet ("\nSLENT:" ^ s) in
            Out.UNKNOWN, None
      | _ -> Out.UNKNOWN, None
  end

(* if all views in deci and composable, use bases  *)
let check_ent_with_bases pdecls is_heap_only is_base_reuse is_linear is_deci e=
  let rec aux_check_ent ante_or_fs=
    match ante_or_fs with
      | a::rest ->
            let e1 = {e with Ccmd.ante = a} in
            let () = Debug.ninfo_hprint (add_str  "e1" (Ccmd.string_of_cmd_ent)) e1 no_pos in
            let r, cex = check_ent_gen pdecls is_heap_only is_base_reuse is_linear is_deci e1 in
            let () = Debug.ninfo_hprint (add_str  "SLENT" (Out.string_of)) r no_pos in
            if r == Out.INVALID then
              r,cex
            else aux_check_ent rest
      | [] -> Out.VALID, None
  in
  let ante_or_ls =  CfUtil.unfold_base_pair pdecls true e.Ccmd.ante in
  aux_check_ent ante_or_ls

let check_ent pdecls (e :Ccmd.cmd_ent) =
  (* sort the view in RHS*)
  let ante_vs = CF.fv e.Ccmd.ante in
  let cons_vs = CF.fv e.Ccmd.cons in
  let () = Debug.ninfo_hprint (add_str  "ante_vs" (Var.string_of_list)) ante_vs no_pos in
  let () = Debug.ninfo_hprint (add_str  "cons_vs" (Var.string_of_list)) cons_vs no_pos in
  if ante_vs!=[] && List.exists (fun v2 -> List.for_all (fun v1 -> not (Var.equal v1 v2) ) ante_vs
  ) cons_vs then
    if CF.is_pure_top e.Ccmd.cons then Out.VALID, None else
      let () = Debug.ninfo_hprint (add_str  "RHS var" (pr_id)) "not in LHS" no_pos in
      Out.INVALID, None
  else
    if CF.isFalse e.Ccmd.cons then
      let r,_ = Kengine.check_sat pdecls e.Ccmd.ante in
      if r == Out.UNSAT then Out.VALID, None
      else if r == Out.SAT then Out.INVALID, None
      else Out.UNKNOWN, None
    else
      let _ , ante_vns,_,p = CF.decompose e.Ccmd.ante in
      let _,_, eqs, _, _ = CP.type_decomp p in
      let () = Debug.ninfo_hprint (add_str  "eqs" (pr_list Var.string_of_pair)) eqs no_pos in
      let e1 = if eqs!=[] then
        let sst = Var.to_parallel_subst eqs in
        let () = Debug.ninfo_hprint (add_str  "sst" (pr_list Var.string_of_pair)) sst no_pos in
        let f1 = CF.subst sst e.Ccmd.ante in
        let a1 = CF.simplify_pure f1 in
        let () = Debug.ninfo_hprint (add_str  "a1" (CF.string_of)) a1 no_pos in
        let f2 = CF.subst sst e.Ccmd.cons in
        {e with Ccmd.ante = a1; Ccmd.cons = f2}
      else e
      in
      (* check whether views are in deci and composable, use bases + buds *)
      let cons_vns, _ = CF.star_decompose e1.Ccmd.cons in
      let vns = ante_vns@cons_vns in
      let is_base_reuse, is_deci, is_compos_linear, is_acyclic, is_heap_only  =  List.fold_left ( fun (r1,r2,r3, r4, r5) vn ->
          try
            let decl = List.find (fun def ->
                Ustr.str_eq def.Cpred.pred_name vn.CpredNode.hpred_name
            ) pdecls in
            let is_linear = match decl.Cpred.pred_composition_vars with
              | Some _ -> true
              | None -> false in
            r1&&decl.Cpred.pred_is_ent_base_reused, r2&&decl.Cpred.pred_is_ent_deci,
            r3&&is_linear, r4&&decl.Cpred.pred_is_acyclic, r5&&decl.Cpred.pred_is_shape_only
        with Not_found -> false, false, false, false, true
      ) (true, true, true, true, true) (vns)
      in
      let is_compos_linear = not !VarGen.ent_tw && is_compos_linear in
      let is_base_reuse = !VarGen.ent_base_reuse && is_deci in
      let () = Debug.ninfo_hprint (add_str  "is_deci" (string_of_bool)) is_deci no_pos in
      let () = Debug.ninfo_hprint (add_str  "is_base_reuse" (string_of_bool)) is_base_reuse no_pos in
      let () = Debug.ninfo_hprint (add_str  "is_compositional_linear" (string_of_bool)) is_compos_linear no_pos in
      let res, cex =  (* if is_base_reuse then *)
      (*   check_ent_with_bases pdecls is_heap_only is_base_reuse is_linear is_deci e1 *)
      (* else *)
        check_ent_gen pdecls is_heap_only is_base_reuse is_compos_linear is_deci e1
      in
      let complete_res = if res == Out.INVALID && not is_deci then
        let () = print_endline_quiet ("\nENT (INVALID -> UNK)") in
        Out.UNKNOWN
      else res
      in
      complete_res, cex
