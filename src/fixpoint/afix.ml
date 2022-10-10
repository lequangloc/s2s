open Globals
open Ustr
open VarGen
open Gen.Basic

module DD = Debug
module TP = Tpdispatcher
module CP = Cpure
module CF = Cformula
module CSH = Csymheap
module CH = Cheap
module CPeN = CpredNode

let qvars_simplify p=
  let elim_eq_quan qvars ps=
    let sst, rest, elim_vars = List.fold_left (fun (acc1, acc2, acc3) p -> begin
      match p with
        | CP.BForm (Term.Eq (Exp.Var (v1, _), (Exp.Var (v2, _)),_)) -> begin
            if Var.mem v1 qvars then (acc1@[(v1,v2)], acc2, acc3@[v1])
            else if Var.mem v2 qvars then
              (acc1@[(v2,v1)], acc2, acc3@[v2])
            else (acc1, acc2@[p], acc3)
          end
        | _ -> (acc1, acc2@[p], acc3)
    end
    ) ([],[],[]) ps in
    elim_vars, List.fold_left (fun acc s ->
        List.map (CP.subst_var [s]) acc
    ) rest sst
  in
  if not (TP.is_sat p) then
    CP.mkFalse no_pos
  else
    let qvars, p1 = CP.split_quantifiers p in
    let () = DD.ninfo_hprint (add_str "qvars" (pr_list Var.string_of)) qvars no_pos in
    let () = DD.ninfo_hprint (add_str "p1" CP.string_of) p1 no_pos in
    let conjs0 = CP.split_conjunctions p1 in
    let conjs0a = List.fold_left (fun acc p ->
        let qvars0, p2 = CP.split_quantifiers p in
        if qvars0=[] then acc@[p] else
          let elim_vars0, p3 = elim_eq_quan qvars0 [p2] in
          let () = DD.ninfo_hprint (add_str "elim_vars0" (pr_list Var.string_of)) elim_vars0 no_pos in
          let rem_vars = Var.diff qvars0 elim_vars0 in
          acc@(List.fold_left (fun acc p ->
              let vars = CP.fv p in
              if Var.diff vars rem_vars == [] then acc
              else  acc@[CP.add_quantifiers rem_vars p]) [] p3)
    ) [] conjs0 in
     let () = DD.ninfo_hprint (add_str "conjs0a" (pr_list CP.string_of)) conjs0a no_pos in
    let elim_vars, conjs1 = elim_eq_quan qvars conjs0a in
    let () = DD.ninfo_hprint (add_str "elim_vars" (pr_list Var.string_of)) elim_vars no_pos in
    let p2 = CP.join_conjunctions conjs1 no_pos in
    let qvars2 = Var.diff qvars elim_vars in
    CP.add_quantifiers qvars2 p2

let lookup_inv invs pos fr_vars rev_sst=
  let rec helper rest_invs=
    match rest_invs with
    | inv::tail ->
      let svl = CP.fv inv in
      let () = DD.ninfo_hprint (add_str "inv (lookup_inv)" CP.string_of) inv no_pos in
      let () = DD.ninfo_hprint (add_str "fr_vars" Var.string_of_list) fr_vars no_pos in
      if Var.intersect svl fr_vars != [] then
        CP.subst_var rev_sst inv
      else helper tail
    | [] -> raise Not_found
  in
  try
    (helper invs)
  with Not_found ->
      (* let ivn = List.nth invs pos in *)
      (* ivn *)
      CP.mkTrue no_pos
let format_str_file s =
  let src = Str.regexp "^" in
  let target = ">> " in
  ("\n"^Str.global_replace src target s)

let compute_inx_aux lower_invs (rel_id, args, defn)=
  let () = Parse_fix.tlist # reset  in
  let fixc_body,fr_vars, rev_sst = Fixcalc.sl2fix_body lower_invs defn rel_id args in
  let fixc_header = Fixcalc.sl2fix_header 1 [rel_id] in
  let input_fixcalc = fixc_body ^ fixc_header in
  let () = Parse_fix.tlist # push_list fr_vars in
  let () = DD.ninfo_hprint (add_str ("Input of fixcalc:") format_str_file) input_fixcalc no_pos in
  let _ =
    if !Globals.gen_fixcalc then Fixcalc.gen_fixcalc_file input_fixcalc else ()
  in
  (* inv *)
  let () = DD.ninfo_hprint (add_str "rev_sst (compute_heap_pure_inv)" (pr_list (pr_pair Var.string_of Var.string_of))) rev_sst no_pos in
  let invs = (Fixcalc.compute_invs input_fixcalc) in
  lookup_inv invs 0 fr_vars rev_sst

let compute_heap_pure_inv_x fml (name:ident) (para_names:Var.t list) is_pure ?srec:(is_self_rec=false) is_linear_compos transed_views:
      (bool * CP.t) =
  (* let vars = para_names in *)
  (* Prepare the input for the fixpoint calculation *)
  let lower_invs = Cpred.get_pred_all_inv transed_views in
  if is_self_rec then (* rel_id, args, rel_defn *)
    let (is_deci, defs) = Dpi.to_pure_self_rec name para_names is_linear_compos lower_invs fml in
    let ls_invs = List.map (fun (rel_id, args, rel_defn) ->
        compute_inx_aux lower_invs (rel_id, args, (CF.mkBase Cheap.HEmp rel_defn no_pos))
    ) defs in
    let () = DD.ninfo_hprint (add_str "ls_invs" (pr_list CP.string_of)) ls_invs no_pos in
    (is_deci, CP.join_conjunctions ls_invs no_pos)
  else
    let inv = compute_inx_aux lower_invs (name, para_names, fml) in
    (false, inv)

(* let compute_heap_pure_inv_x fml (name:ident) (para_names:Var.t list) is_pure ?srec:(is_self_rec=false) is_linear_compos transed_views: *)
(*       (bool * CP.t) = *)
(*   (\* let vars = para_names in *\) *)
(*   (\* Prepare the input for the fixpoint calculation *\) *)
(*   let lower_invs = Cpred.get_pred_inv transed_views in *)
(*   let () = Parse_fix.tlist # reset  in *)
(*   let is_deci, input_fixcalc, fr_vars, rev_sst = *)
(*     if is_self_rec then (\* rel_id, args, rel_defn *\) *)
(*       let (is_deci, defs) = Dpi.to_pure_self_rec name para_names is_linear_compos lower_invs fml in *)
(*       let fixc_body,fr_vars, rev_sst = Fixcalc.sl2fix_body lower_invs *)
(*  (CF.mkBase Cheap.HEmp rel_defn no_pos) rel_id args in *)
(*       let fixc_header = Fixcalc.sl2fix_header 1 [rel_id] in *)
(*       (is_deci, fixc_body ^ fixc_header, fr_vars, rev_sst) *)
(*     else *)
(*       let fixc_body,fr_vars, rev_sst = Fixcalc.sl2fix_body lower_invs fml name para_names in *)
(*       let fixc_header = Fixcalc.sl2fix_header 1 [name] in *)
(*       (false, fixc_body ^ fixc_header, fr_vars, rev_sst) *)
(*   in *)
(*   let () = Parse_fix.tlist # push_list fr_vars in *)
(*   let () = DD.info_hprint (add_str ("Input of fixcalc:") format_str_file) input_fixcalc no_pos in *)
(*   let _ = *)
(*     if !Globals.gen_fixcalc then Fixcalc.gen_fixcalc_file input_fixcalc else () *)
(*   in *)
(*   (\* inv *\) *)
(*   let () = DD.ninfo_hprint (add_str "rev_sst (compute_heap_pure_inv)" (pr_list (pr_pair Var.string_of Var.string_of))) rev_sst no_pos in *)
(*   let invs = (Fixcalc.compute_invs input_fixcalc) in *)
(*   is_deci, lookup_inv invs 0 fr_vars rev_sst *)

let compute_heap_pure_inv fml (name:ident) (para_names:Var.t list) is_pure ?srec:(is_self_rec=false) is_linear_compos lower_invs: (bool * CP.t) =
  let pr1 = Cpure.string_of in
  let pr2 = Cformula.string_of in
  Debug.no_3 "compute_heap_pure_inv" (pr2) pr_id Var.string_of_list (pr_pair string_of_bool pr1)
      (fun _ _ _ ->  compute_heap_pure_inv_x fml name para_names is_pure ~srec:is_self_rec is_linear_compos lower_invs)
    fml name para_names

(* do not need to call fixcalc
   replace pred --> its inv
   abs (equi-sat) the points-to predicates
*)
let compute_inv_no_rec name vars fml is_pure lower_views=
  let aux qvars fb=
    let preds, ptos = CH.star_decompose fb.CSH.base_heap in
    let p1 = List.fold_left (fun acc_p pred ->
        let pdecl = List.find (fun decl ->
            Ustr.str_eq pred.CPeN.hpred_name decl.Cpred.pred_name) lower_views in
        let sst = List.combine pdecl.Cpred.pred_vars pred.CPeN.hpred_arguments in
        let subst_inv = CP.subst_var sst pdecl.Cpred.pred_pure_inv in
        CP.mkAnd acc_p subst_inv no_pos
    ) fb.CSH.base_pure preds in
    (* point-to predicates *)
    let p2 = CptoNode.to_abs_pure_form ptos in
    let qf_inv = CP.mkAnd p1 p2 no_pos in
    let inv = CP.mkExists qvars qf_inv no_pos in
    let is_deci = (List.fold_left (fun acc_deci pred ->
        let pdecl = List.find (fun decl ->
            Ustr.str_eq pred.CPeN.hpred_name decl.Cpred.pred_name) lower_views in
        acc_deci && pdecl.Cpred.pred_is_sat_deci
    ) true preds) in
    is_deci, inv
  in
  let rec helper f= match f with
    | CF.Base fb -> aux [] fb
    | CF.Exists (fb, qvars) -> aux (Var.remove_dups qvars) fb
    | CF.Or (f1, f2, pos) -> let r1, p1 = helper f1 in
      let r2, p2 = helper f2 in
      (r1 && r2), CP.mkOr p1 p2 pos
  in
  helper fml

let compute_inv_x name vars fml is_pure rec_knd is_linear_compos lower_views pf =
  let inv_self_rec is_selfrec =
    let is_deci, new_pf0 = compute_heap_pure_inv fml name vars is_pure ~srec:is_selfrec is_linear_compos lower_views in
    let new_pf = (* exists quantified *)
      let svl = CP.fv new_pf0 in
      let qsv = Var.diff svl vars in
      if qsv = [] then new_pf0 else
        if Var.diff svl qsv == [] then CP.mkTrue no_pos
        else
          qvars_simplify (CP.mkExists qsv new_pf0 no_pos)
    in
    is_deci, new_pf
  in
  if not !Globals.infer_inv then false, pf
  else
    let is_deci, new_pf = if rec_knd == NOREC then
      (* if it is no recursive, do not need to call fixcalc *)
      compute_inv_no_rec name vars fml is_pure lower_views
    else
      inv_self_rec (rec_knd == SELFREC)
    in
    let check_imply = TP.imply new_pf pf in
    let stronger_inv =
      if check_imply then
        let () = DD.ninfo_hprint (add_str ("new 1 inv("^name^")") Cpure.string_of) new_pf no_pos in
        let () = print_endline_quiet "" in
        new_pf
      else pf
    in is_deci, stronger_inv

let compute_inv name vars fml is_pure rec_knd is_linear_compos lower_views pf =
  let pr1 = Cformula.string_of in
  let pr2 = Cpure.string_of in
  Debug.no_4 " compute_inv" pr_id Var.string_of_list ( pr1) pr2
      (pr_pair string_of_bool pr2)
      (fun _ _ _ _ -> compute_inv_x name vars fml is_pure rec_knd is_linear_compos lower_views pf)
      name vars fml pf

(*compute invs of views in one strongest connected component*)
let do_compute_inv_scc mutrec_preds cpreds=
  let rec lookup_map vmaps vname0=
    match vmaps with
    | [] -> raise Not_found
    | (vname,b,c):: rest -> if str_eq vname vname0 then
        (vname,b,c) else
        lookup_map rest vname0
  in
  let update_pred invs pos vmaps pred all_rev_sst=
    try
      let (vname, fr_vars, rev_sst) = lookup_map vmaps pred.Cpred.pred_name in
      let () = DD.ninfo_hprint (add_str "rev_sst" (pr_list (pr_pair Var.string_of Var.string_of))) rev_sst no_pos in
      let new_pf = lookup_inv invs pos fr_vars rev_sst in
      let _ = DD.ninfo_hprint (add_str ("new 2 inv(" ^ vname^")") Cpure.string_of) new_pf no_pos in
      let () = DD.ninfo_hprint (add_str "new_pf" Cpure.string_of) new_pf no_pos in
      begin
        let () = pred.Cpred.pred_pure_inv <- new_pf in
        pred
      end
    with _ -> pred
  in
  (**************************************************)
  let _ = DD.ninfo_hprint (add_str ("do_compute_inv_scc") (pr_list_ln Cpred.string_of)) cpreds no_pos in
  if (not !Globals.infer_inv) ||
    (List.for_all (fun p -> List.for_all (fun v -> (Var.is_node v)) p.Cpred.pred_vars) cpreds)
  then
    cpreds
  else
    (* get all preds of the loop
       subst inv of their depent (lower) preds
      (remember to remove members of the loop)
    *)
    let mutrec_views, rest = List.partition (fun v ->
        Gen.BList.mem_eq str_eq v.Cpred.pred_name mutrec_preds
      ) cpreds in
    let lower_invs = Cpred.get_pred_all_inv rest in
    let () = Parse_fix.tlist # reset in
    (*gen cf of each view*)
    let fixc_bodys, vnames, vmaps = List.fold_left (fun (r1,r2,r3) p ->
        let fixc_body, fr_vars, rev_sst = Fixcalc.sl2fix_body lower_invs
          p.Cpred.pred_formula p.Cpred.pred_name p.Cpred.pred_vars in
        let () = Parse_fix.tlist # push_list fr_vars in
        (r1 ^ "\n" ^ fixc_body, r2@[p.Cpred.pred_name], r3@[(p.Cpred.pred_name,fr_vars, rev_sst)])
      ) ("",[],[]) cpreds in
    let fixc_header = Fixcalc.sl2fix_header 3 vnames in
    let input_fixcalc  =  fixc_bodys ^ fixc_header in
    let () = DD.ninfo_hprint (add_str "Input of fixcalc " pr_id) input_fixcalc no_pos in
    let _ =
      if !Globals.gen_fixcalc then Fixcalc.gen_fixcalc_file input_fixcalc else ()
    in
    (* Call the fixpoint calculation *)
    let invs = (Fixcalc.compute_invs input_fixcalc) in
    let () = DD.ninfo_hprint (add_str "invs" (pr_list Cpure.string_of)) invs no_pos in
    (*get result and revert back*)
    (*set invs + flags*)
    let all_rev_sst = List.fold_left (fun r (_,_,sst) -> r@sst) [] vmaps in
    let r,_ = List.fold_left (fun (res,pos) pred ->
        let npred = update_pred invs pos vmaps pred all_rev_sst in
        (res@[npred], pos+1)
    ) ([], 0) cpreds in
    r

(* a wrapper for debug *)
let compute_inv_scc mutrec_preds preds =
  let pr1 = pr_list pr_id in
  let pr2 v = (pr_pair pr_id (Cpure.string_of)) (v.Cpred.pred_name,v.Cpred.pred_pure_inv) in
  Debug.no_2 "compute_inv_scc" pr1 (pr_list pr2)  (pr_list pr2)
      (fun _ _ -> do_compute_inv_scc mutrec_preds preds)
      mutrec_preds preds


let compute_fixpt_x mutrec_vnames vn view_sv_vars n_un_str is_pure rec_knd is_linear_compos transed_views inv_pf =
  if List.for_all Var.is_node view_sv_vars then true, inv_pf
  else
    let is_deci, new_pf = if Gen.BList.mem_eq (fun s1 s2 -> String.compare s1 s2 = 0)
      vn mutrec_vnames then false, inv_pf
    else compute_inv vn view_sv_vars n_un_str is_pure rec_knd is_linear_compos transed_views inv_pf
    in is_deci, new_pf

let compute_fixpt mutrec_vnames vn view_sv_vars n_un_str is_pure
      rec_knd is_linear_compos transed_views inv_pf =
  let pr1 = add_str "view_name" pr_id in
  let pr2 = add_str "inv_pf" CP.string_of in
  let pr3 v = (pr_pair pr_id (Cpure.string_of)) (v.Cpred.pred_name,v.Cpred.pred_pure_inv) in
  Debug.no_5 "compute_fixpt" pr1 Var.string_of_list pr2  string_of_rec_kind (pr_list_ln pr3) (pr_pair string_of_bool pr2)
      (fun _ _ _ _ _ -> compute_fixpt_x mutrec_vnames vn view_sv_vars n_un_str is_pure rec_knd is_linear_compos transed_views inv_pf)
      vn view_sv_vars inv_pf rec_knd transed_views
