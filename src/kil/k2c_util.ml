open Globals
open VarGen
open Gen.Basic
open Exc.GTable
open Cgraph


module IF = Iformula
module CF = Cformula
module CH = Cheap
module CHN = CpredNode

let order_preds_x (pred_decls : Ipred.pred_decl list) pred_rec pred_scc : Ipred.pred_decl list * (ident list list) * (ident list) * (ident list) list =
(***************************************************)
            (**********AUX**********)
(***************************************************)
  let build_graph vdefs =
    let tmp =
      List.map
        (fun vdef -> K.gen_name_pairs_cof pred_decls
            vdef.Ipred.pred_name vdef.Ipred.pred_formula)
        vdefs
    in
    let () = List.iter (fun vd ->
        let n = vd.Ipred.pred_name in
        let lst = K.gen_name_pairs_cof vdefs n vd.Ipred.pred_formula in
        Cgraph.pred_scc_obj # replace n (List.map snd lst)
      ) vdefs in
    let selfrec = List.filter (fun l -> List.exists (fun (x,y) -> x=y) l) tmp in
    let selfrec = List.map (fun l -> fst (List.hd l)) selfrec in

    let edges = List.concat tmp in
    let g = NG.create () in
    let todo_unk = (List.map (fun (v1, v2) ->
        NG.add_edge g (NG.V.create v1) (NG.V.create v2))
        edges) in
    let scclist = NGComponents.scc_list g in
    let mr = List.filter (fun l -> (List.length l)>1) scclist in
    (* let str = pr_list (pr_list pr_id) mr in *)
    let mutrec = List.concat mr in
    let selfrec = (Gen.BList.difference_eq (=) selfrec mutrec) in
    (* let () = print_endline ("Self Rec :"^selfstr) in *)
    let (self_rec, mutrec) = Cgraph.pred_scc_obj # get_rec in
    let scclist = Cgraph.pred_scc_obj # get_scc in
    let n_pred_rec = selfrec@mutrec in
    let n_pred_scc = scclist in
    (* let () = y_tinfo_hp (add_str "\n" pr_id) (view_scc_obj # string_of) in *)
    Cgraph.pred_scc_obj # get_graph, n_pred_rec, n_pred_scc
  in
  let rec reorder_preds (view_decls : Ipred.pred_decl list)
      (ordered_names : ident list) =
    match ordered_names with
      | n :: rest ->
            let (n_view, rest_decls) =
              List.partition (fun v -> v.Ipred.pred_name = n) view_decls in
            let (rest_views, new_rest_decls) =
              reorder_preds rest_decls rest
            in
            (* n_view should contain only one views *)
            ((n_view @ rest_views), new_rest_decls)
      | [] -> ([], view_decls) in
  (***************************************************)
  (**********END AUX**********)
  (***************************************************)
  let () = Debug.ninfo_hprint (add_str "order_preds" (pr_list Ipred.string_of)) pred_decls no_pos in
  let g,n_pred_rec, n_pred_scc = build_graph pred_decls in
  let () = Debug.ninfo_hprint (add_str "n_pred_rec" (pr_list pr_id)) n_pred_rec no_pos in
  (* take out the pred names in reverse order *)
  let pred_names = ref ([] : ident list) in
  let store_name n = pred_names := n :: !pred_names in
  let () = (TopoNG.iter store_name g) in

  (* now reorder the preds *)
  let (r1, r2) = reorder_preds pred_decls !pred_names in
  (r1 @ r2, List.filter (fun ls -> List.length ls > 1) n_pred_scc ,n_pred_rec, n_pred_scc)

let order_preds (pred_decls : Ipred.pred_decl list) pred_rec pred_scc : Ipred.pred_decl list * (ident list list) * (ident list) * (ident list) list =
  let pr x = Ustr.string_of_ident_list (List.map (fun v -> v.Ipred.pred_name) x) in
  let pr2  = (pr_list (pr_list pr_id)) in
  let pr_out = pr_quad pr pr2 (pr_list pr_id) (pr_list (pr_list pr_id)) in
  Debug.no_1 "order_preds" pr pr_out
      (fun _  -> order_preds_x pred_decls pred_rec pred_scc) pred_decls

let repair_type sst_args_typ=
  let rec aux ls res=
    match ls with
      | (sv, t)::rest -> begin
          let nsv = match sv.Var.t with
            | TVar _ -> {sv with Var.t = t}
            | _ -> sv
          in aux rest (res@[nsv])
        end
      | [] -> res
  in aux sst_args_typ []

let update_view_arg_well_types (vn, typs) f0=
  let rec helper_heap h=
    match h with
      | CH.Star (h1, h2, pos) -> CH.Star (helper_heap h1, helper_heap h2, pos)
      | CH.PredNode hp -> if Ustr.str_eq hp.CHN.hpred_name vn then
          let n_args = repair_type (List.combine hp.CHN.hpred_arguments typs) in
          CH.PredNode {hp with CHN.hpred_arguments = n_args}
        else h
      | _ -> h
  in
  let rec helper f=
    match f with
      | CF.Base fb -> CF.Base {fb with Csymheap.base_heap = helper_heap fb.Csymheap.base_heap}
      | CF.Exists (fb, qvars) -> CF.Exists ({fb with Csymheap.base_heap = helper_heap fb.Csymheap.base_heap}, qvars)
      | CF.Or (f1, f2, pos) -> CF.Or (helper f1, helper f2, pos)
  in helper f0

let get_view_arg_well_types ?wt:(wt=true) vn f0=
  let rec helper_heap h=
    match h with
      | CH.Star (h1, h2, _) -> begin
          let r1 = helper_heap h1 in
          match r1 with
            | Some _ -> r1
            | None -> helper_heap h2
        end
      | CH.PredNode hp -> if Ustr.str_eq hp.CHN.hpred_name vn then
          if List.for_all (fun v -> match v.Var.t with
              | TVar _ -> not wt
              | _ -> wt) hp.CHN.hpred_arguments then
            Some (vn, List.map Var.type_of hp.CHN.hpred_arguments)
          else None
        else None
      | _ -> None
  in
  let rec helper f=
    match f with
      | CF.Base fb
      | CF.Exists (fb, _) -> helper_heap fb.Csymheap.base_heap
      | CF.Or (f1, f2, _) -> begin
          let r1 = helper f1 in
          match r1 with
            | Some _ -> r1
            | None -> helper f2
        end
  in helper f0

let update_type_mutrec_x top_mutrec_preds last_pred=
  let rec find_pairwise_diff sst res=
    match sst with
      | (t1, t2):: rest -> let new_res =
          if t1 = t2 then res
          else res@[(t1,t2)]
        in find_pairwise_diff rest new_res
      | [] -> res
  in
  let rec fix_backward ls0 pred=
    let (vn0, types0) = pred.Cpred.pred_name, List.map Var.type_of pred.Cpred.pred_vars in
    (* let ls = List.map (fun p -> {p with Cpred.pred_formula = update_view_arg_well_types (vn0, types0) p.Cpred.pred_formula;}) ls0 in *)
    let ls, tis = List.fold_left (fun (r1, r2) p ->
        let r = get_view_arg_well_types ~wt:false vn0 p.Cpred.pred_formula in
        match r with
          | Some (_, bad_types) -> begin
                let t_sst = find_pairwise_diff (List.combine bad_types types0) [] in
                if t_sst = [] then (r1@[p], r2)
                else
                  let n_vars = List.map (fun sv -> begin
                    try
                      let _, n_t = List.find (fun (t1, _) -> t1 = sv.Var.t) t_sst in
                      {sv with Var.t = n_t}
                    with Not_found -> sv
                  end
                  ) p.Cpred.pred_vars in
                  let np = {p with Cpred.pred_vars = n_vars;
                      Cpred.pred_formula = CF.subst_type t_sst p.Cpred.pred_formula;
                  } in
                  (r1@[np], r2@t_sst)
            end
          | None -> (r1@[p], r2)
    ) ([],[]) ls0 in
    let () = Debug.ninfo_hprint (add_str "ls" (pr_list Cpred.string_of))
      ls no_pos in
    [pred]@ls, tis
    (* match ls with *)
    (*   | [] -> [pred]@res *)
    (*   | pred2::rest -> begin *)
    (*         if List.exists (fun v -> match v.Var.t with *)
    (*           | TVar _ -> true *)
    (*           | _ -> false *)
    (*         ) pred2.Cpred.pred_vars then *)
    (*           (\* find the first view pred2 which is well-typed in pred and res *\) *)
    (*           let view_well_type = get_view_arg_well_types pred2.Cpred.pred_name pred.Cpred.pred_formula in *)
    (*           match view_well_type with *)
    (*             | Some (vn, types) -> begin *)
    (*                 (\* to fix *\) *)
    (*                 let n_pred2 = {pred2 with *)
    (*                     Cpred.pred_vars = repair_type (List.combine pred2.Cpred.pred_vars types); *)
    (*                     Cpred.pred_formula = update_view_arg_well_types (vn, types) pred2.Cpred.pred_formula; *)
    (*                 } in *)
    (*                 let n_res = List.map (fun p -> *)
    (*                     {p with Cpred.pred_formula = update_view_arg_well_types (vn, types) p.Cpred.pred_formula;} *)
    (*                 ) res in *)
    (*                 fix_backward rest n_pred2 ([pred]@n_res) *)
    (*               end *)
    (*             | None -> fix_backward rest pred2 ([pred]@res) *)
    (*         else *)
    (*           fix_backward rest pred2 ([pred]@res) *)
    (*     end *)
  in
  fix_backward (List.rev top_mutrec_preds) last_pred

let update_type_mutrec top_mutrec_preds last_pred=
  let pr1 = Cpred.string_of in
  let pr2 = pr_pair (pr_list_ln pr1) (pr_list (pr_pair string_of_typ string_of_typ)) in
  Debug.no_2 "update_type_mutrec" (pr_list_ln pr1) pr1 pr2
      (fun _ _ -> update_type_mutrec_x top_mutrec_preds last_pred)
      top_mutrec_preds last_pred
