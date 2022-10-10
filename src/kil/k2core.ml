open Globals
open Ustr
open VarGen
open Gen.Basic
open Error
open Exc.GTable

open Cgraph
open K2c_util

module TI = Typeinf

module IF = Iformula
module ISH = Isymheap
module IP = Ipure
module IT = Iterm
module IE = Iexp
module IH = Iheap

module CFU = CfUtil
module CF = Cformula
module CSH = Csymheap
module CP = Cpure
module CT = Term
module CE = Exp
module K2C = K2c_trans

(***************************************************)
          (**********MAIN CLASS**********)
(***************************************************)
class k2c src_files parse=  object(self)
  val m_src_files = src_files
  val m_parser = parse
  val m_kdata = new Dmain.kdata src_files parse
  (* list of scc views that are in mutual-recursion *)
  val mutable m_pred_scc : (ident list) list = []
  (* list of views that are self recursive *)
  val mutable m_pred_rec : (ident list) = []


  method trans_field ((t, c), pos) =
    (((m_kdata # check_exist_type t pos), c), [])

  method trans_data_decl  ddef=
    let fields = List.map self#trans_field
      ((* Inode.expand_inline_fields prog.I.prog_data_decls *) ddef.Inode.data_fields)
    in
    let res = {
        Cnode.data_name = ddef.Inode.data_name;
        Cnode.data_pos = ddef.Inode.data_pos;
        Cnode.data_fields = fields;
        Cnode.data_fields_new =  List.map (fun ((t,i), v) -> (Var.mk t i Unprimed, v)) fields;
        Cnode.data_parent_name = ddef.Inode.data_parent_name;
    } in
    let () = Debug.ninfo_hprint (add_str "[trans_data] output" Cnode.string_of) res no_pos in
    res

  method trans_data_decls ddecls=
    List.map self # trans_data_decl ddecls

  method find_rec_kind pred_name=
    let () = Debug.ninfo_hprint (add_str "pred_name" pr_id) pred_name no_pos in
    let () = Debug.ninfo_hprint (add_str "m_pred_rec" (pr_list pr_id)) m_pred_rec no_pos in
    let () = Debug.ninfo_hprint (add_str "m_pred_scc" (pr_list (pr_list pr_id))) m_pred_scc no_pos in
    if Gen.BList.mem_eq Ustr.str_eq pred_name m_pred_rec then
      SELFREC
    else begin
      try
        let mutrec_grp = List.find (fun grp ->
            Gen.BList.mem_eq Ustr.str_eq pred_name grp
        ) m_pred_scc in
        if List.length mutrec_grp > 1 then
          MUTREC (mutrec_grp)
        else
          NOREC
      with Not_found -> NOREC
    end

  method trans_pred_decl mutrec_preds cur_cpreds ann_typs pdef=
    let data_name = pdef.Ipred.pred_data_name in
    let () = Debug.ninfo_hprint (add_str "trans_decl" pr_id) pdef.Ipred.pred_name no_pos in
    let vtv = pdef.Ipred.pred_typed_vars in
    let tlist = List.map (fun (t,c) -> (c,{TI.sv_info_kind=t; TI.id=fresh_int() })) vtv in
    let orig_tl = ann_typs@tlist in
    let iform = K2C.normalize_formula (m_kdata # get_idata_decls ())  pdef.Ipred.pred_formula in
    let (n_tl,cf) = K2C.trans_disj_formula (m_kdata # get_idata_decls ()) (m_kdata # get_ipred_decls ()) (m_kdata # get_irel_decls ()) true (pdef.Ipred.pred_vars)
     iform (orig_tl) in
    let () = Debug.ninfo_hprint (add_str "orig_tl" TI.string_of_tlist) orig_tl no_pos in
    let () = Debug.ninfo_hprint (add_str "n_tl" TI.string_of_tlist) n_tl no_pos in
    let cf = CfUtil.sequentialize_and_unfold_flat_views cur_cpreds  cf in
    let () = Debug.ninfo_hprint (add_str "cf 3" CF.string_of) cf no_pos in
    let inv = pdef.Ipred.pred_invariant in
    let n_tl = TI.gather_type_info_pure (m_kdata # get_irel_decls ()) inv n_tl in
    let inv_pf = K2C.trans_pure_formula inv n_tl in
    (* pf - user given invariant in core form *)
    let inv_pf = CP.arith_simplify inv_pf in
    let cf_fv = List.map Var.name_of (CF.fv cf) in
    let pf_fv = List.map Var.name_of (CP.fv inv_pf) in

    if (List.mem res_name cf_fv) || (List.mem res_name pf_fv) then
      Gen.report_error pdef.Ipred.pred_pos
          "res is not allowed in predicate either definition or invariant"
    else begin
      let pos = pdef.Ipred.pred_pos in
      let pred_sv_vars = List.map (fun c-> K2C.trans_var (c, Unprimed) n_tl pos)
        pdef.Ipred.pred_vars in
      (* let self_c_var = Var.mk (Named data_name) Globals.self Unprimed in *)
      let null_c_var = Var.null_var in
      let () =  Debug.ninfo_hprint (add_str "pred_sv_vars" Var.string_of_list) pred_sv_vars no_pos in
      let cf =
        let vs1 = (CF.fv cf) in
        let () =  Debug.ninfo_hprint (add_str "vs1" Var.string_of_full_list) vs1 no_pos in
        let vs2 = (null_c_var::(*self_c_var::*)pred_sv_vars) in
        let vs1a = CP.fv inv_pf in
        let vs1 = vs1@vs1a in
        let ffv = Var.diff vs1 vs2 in
        let ffv = List.filter (fun v -> not (Var.is_rel_typ v)) ffv in
        (* filter out intermediate dereference vars
           and update them to view vars *)

        let ffv = List.filter (fun v ->
            let is_deref_var = Var.is_inter_deference_spec_var v in
            if (is_deref_var) then (
                pdef.Ipred.pred_vars <- pdef.Ipred.pred_vars @ [v.Var.id];
            );
            not (is_deref_var)
        ) ffv in
        if (ffv!=[]) then
          let () = Gen.report_warning no_pos ("free variables "^(Var.string_of_list ffv)^" in pred def "^pdef.Ipred.pred_name^" ")
          in
          CF.add_quantifiers ffv cf
        else cf
      in
      let typed_vars = List.map ( fun sv -> (sv.Var.t,sv.Var.id)) pred_sv_vars in
      let () = pdef.Ipred.pred_typed_vars <- typed_vars in
      let is_prim_v = pdef.Ipred.pred_is_prim in
      let () =  Debug.ninfo_hprint (add_str "pred_name" pr_id) pdef.Ipred.pred_name no_pos in

      let () = Debug.ninfo_hprint (add_str "body 1" CF.string_of) cf no_pos in
      let rec_kind = self # find_rec_kind pdef.Ipred.pred_name in
      let is_pure = CFU.is_pure cur_cpreds [pdef.Ipred.pred_name] cf in
      (* compute better over inv: new_pf >= pf *)
      let () = Debug.ninfo_hprint (add_str "is_pure" string_of_bool) is_pure no_pos in
      let vn = pdef.Ipred.pred_name in
      (* the predicate is precise?, bw(backware parameters) *)
      let roots, precise_vars, bw_vars, is_acyclic, is_compsable, is_local_acyclic_list = CfUtil.check_pred_precise cur_cpreds vn pred_sv_vars cf in
      let is_deci2, new_pf = Afix.compute_fixpt mutrec_preds vn pred_sv_vars cf is_pure rec_kind (is_compsable && precise_vars!=None) cur_cpreds inv_pf in
      let is_deci1, is_linear_compose = match precise_vars with
        | Some (( root_prs, cyc_local_prs, acyc_local_prs, nonlocal_prs, nonlocal_ext_prs, others), _) -> roots!=[],
              (is_compsable)
        | None -> false, false in
      Debug.ninfo_hprint (add_str "inv_pf" Cpure.string_of) inv_pf no_pos;
      Debug.ninfo_hprint (add_str "new_pf" Cpure.string_of) new_pf no_pos;
      let pred_pure_inv =  new_pf in
      Debug.ninfo_hprint (add_str "name" (fun x -> x)) vn no_pos;
      let () = Debug.ninfo_hprint (add_str "pred_vars" Var.string_of_list) pred_sv_vars no_pos in
      let cf_w_ctx =
        CfUtil.compute_br_inv cur_cpreds vn pred_sv_vars cf roots precise_vars
      in
      let unfolded_formula = if !VarGen.disable_extend_htrue then []
      else CfUtil.extend_pred_defn vn pred_sv_vars roots precise_vars cf in
      (* set up progressing step *)
      let cf1 = CfUtil.set_progressing_step cf in
      let cpred = {
          Cpred.pred_name = vn;
          Cpred.pred_vars = pred_sv_vars;
          Cpred.pred_formula = cf1;
          Cpred.pred_unfolded_formula = unfolded_formula;

          Cpred.pred_is_prim = is_prim_v;
          Cpred.pred_parent_name = None;
          Cpred.pred_data_name = data_name;

          Cpred.pred_formula_w_ctx = cf_w_ctx;

          (* Cpred.pred_order = denp_order; *)
          Cpred.pred_roots = roots;
          Cpred.pred_composition_vars = precise_vars;
          Cpred.pred_bw_tars = bw_vars;

          Cpred.pred_pure_inv = pred_pure_inv;
          Cpred.pred_base = ([],[]);
          Cpred.pred_rec = rec_kind;
          Cpred.pred_is_sat_deci = is_deci1 || is_deci2;
          Cpred.pred_is_ent_deci = is_deci1 || is_deci2;
          Cpred.pred_is_shape_only =  List.for_all (Var.is_node) pred_sv_vars;
          Cpred.pred_is_ent_base_reused = false;
          Cpred.pred_is_acyclic = is_acyclic;
          Cpred.pred_is_pure_acyclic = is_local_acyclic_list;
          Cpred.pred_is_composable = is_linear_compose;
          Cpred.pred_compose_rule_same_ext_src =[];
          Cpred.pred_compose_rule_diff_ext_src = [];
          Cpred.pred_strengthen_rules = [];
          Cpred.pred_is_pure = is_pure;

          Cpred.pred_pos = pdef.Ipred.pred_pos;
      } in
      cpred
    end


  method trans_pred_decls all_mutrec_preds (typ_pdecls: (Ipred.pred_decl * ((Globals.ident * Typeinf.var_info) list) )list)=
    let () = Debug.ninfo_hprint (add_str "all_mutrec_preds" (pr_list (pr_list pr_id)))
      all_mutrec_preds no_pos in
    let all_mutrec_vnames = (List.concat all_mutrec_preds) in

    let cmp_list_str ls1 ls2=
      ((List.length ls1) = (List.length ls2)) &&
          Gen.BList.difference_eq Ustr.str_eq ls1 ls2 = []
    in
    let rec compute_base_pairs cpreds res=
      match cpreds with
        | p::rest -> begin
            let () = Debug.ninfo_hprint (add_str ("compute_base_pairs: pred.Ipred.pred_name") pr_id) p.Cpred.pred_name no_pos in
            let sst, rev_sst = List.fold_left (fun (r1, r2) v ->
                let v1 = Var.fresh_var v in
                (r1@[(v, v1)], r2@[(v1, v)])
            ) ( [], []) (Var.remove_dups p.Cpred.pred_vars)  in
            let fr_vars = List.map (Var.subst sst) p.Cpred.pred_vars in
            let vn = CF.mkBase (CH.PredNode (CpredNode.mk p.Cpred.pred_name true fr_vars (* p.Cpred.pred_vars *) p.Cpred.pred_pos)) (CP.mkTrue no_pos) p.Cpred.pred_pos in
            (* update sat-deci, in case mutrec: typeinf is not precise *)
            let is_deci = if List.for_all Var.is_node p.Cpred.pred_vars then true else p.Cpred.pred_is_sat_deci in
            let is_link_back_heap_only = true in
            (* is_link_back_heap_only is only false with
               elastic properties*)
            let r, bases, buds = SlSat.build_base_pair_or_sat (res@cpreds)
              p.Cpred.pred_is_shape_only is_link_back_heap_only false
              false true vn Com.tree_bound Com.tree_size_sat in
            let () = Debug.ninfo_hprint (add_str ("compute_base_pairs: pred.Ipred.pred_name") pr_id) p.Cpred.pred_name no_pos in
            let () = Debug.ninfo_hprint (add_str ("Outcome") Out.string_of) r no_pos in
            let n_p = match r with
              | Out.SAT ->
                    {p with Cpred.pred_base = (List.map (CF.subst rev_sst) bases, List.map (CF.subst rev_sst) buds);
                    Cpred.pred_is_sat_deci = is_deci;}
              | Out.UNSAT -> {p with Cpred.pred_base = ([CF.mkFalse no_pos], []);
                    Cpred.pred_is_sat_deci = is_deci;}
              | _ -> p
              in
              compute_base_pairs rest (res@[n_p])
          end
        | [] -> res
    in
    let rec gen_composition_lemmas cpreds res=
      match cpreds with
        | p::rest -> begin
            let (compose_rules_same,compose_rules_diff) = match p.Cpred.pred_composition_vars with
              | Some (( root_prs, local_precise_prs, local_ext_prs, nonlocal_precise_prs, nonlocal_ext_prs, _), _) ->
                  if p.Cpred.pred_is_composable then
                    RuleSyn.generate_composable_rule (cpreds@res)
                        p.Cpred.pred_name p.Cpred.pred_vars p.Cpred.pred_pure_inv p.Cpred.pred_is_acyclic root_prs local_precise_prs local_ext_prs nonlocal_precise_prs nonlocal_ext_prs
              else ([],[])
              | None -> ([], [])
            in
            let n_p = {p with Cpred.pred_compose_rule_same_ext_src = compose_rules_same;
                Cpred.pred_compose_rule_diff_ext_src = compose_rules_diff;} in
            gen_composition_lemmas rest (res@[n_p])
          end
        | [] -> res
    in
    let rec gen_strengthen_lemmas cpreds res=
      match cpreds with
        | p::rest -> begin
            let lemmas = if (List.length p.Cpred.pred_vars) > 2 then
              RuleSyn.generate_strengthen_rules (cpreds@res)  p
            else []
            in
            let n_p = {p with Cpred.pred_strengthen_rules = lemmas;
            } in
            gen_strengthen_lemmas rest (res@[n_p])
          end
        | [] -> res
    in
    let trans_one_scc (cur_cpreds, cur_mutrec_preds, rectify_tis) (pred,typ_infos)=
      let mutrec_preds = if Gen.BList.mem_eq str_eq
        pred.Ipred.pred_name all_mutrec_vnames
      then (cur_mutrec_preds@[pred.Ipred.pred_name])
      else cur_mutrec_preds
      in
      let () = Debug.ninfo_hprint (add_str ("trans_one_scc: pred.Ipred.pred_name") pr_id) pred.Ipred.pred_name no_pos in
      let npred = self # trans_pred_decl mutrec_preds cur_cpreds typ_infos pred in
      (* to compute invs for mut-rec preds *)
      let cur_cpreds2, mutrec_preds, rectis_out = if mutrec_preds!=[] &&
        Gen.BList.mem_eq cmp_list_str mutrec_preds all_mutrec_preds
      then
        (* rectify types of parameters of mutual recursive *)
        let transed_views1, rectis =
          if List.length cur_cpreds > 0 then
            K2c_util.update_type_mutrec cur_cpreds npred
          else cur_cpreds@[npred], rectify_tis  in
        let cur_cpreds3 = Afix.compute_inv_scc mutrec_preds transed_views1 in
        (cur_cpreds3, [] (*complete one mutrec, reset it*), rectis)
      else (cur_cpreds@[npred], mutrec_preds, [])
      in
      (cur_cpreds2, mutrec_preds,rectify_tis@rectis_out)
    in
    (*******************************)
    let cpreds0,_,_ = List.fold_left trans_one_scc ([],[],[]) typ_pdecls in
    (* compute base pair *)
    let cpreds = if !VarGen.ent_tw || (!VarGen.sat_base_reuse &&
        (List.exists (fun p -> not p.Cpred.pred_is_shape_only ) cpreds0))
      || (!VarGen.ent_base_reuse && not (List.for_all (fun p -> p.Cpred.pred_is_acyclic && p.Cpred.pred_is_composable) cpreds0)  && (m_kdata #get_ient_queries ()) != [])
    then
      compute_base_pairs cpreds0 []
    else cpreds0 in
    let cpreds = if (m_kdata #get_ient_queries ()) != [] then
      let cpreds1 = gen_composition_lemmas cpreds [] in
      if List.length cpreds > 1 then
        gen_strengthen_lemmas cpreds1 []
      else cpreds1
    else cpreds in
    cpreds

  method trans_vc_sat fs=
    let trans_one (f,e)=
      let iform = K2C.normalize_formula (m_kdata # get_idata_decls ())  f in
      let orig_tl =  [] in
      let vars = [] in
      let (n_tl,cf) = K2C.trans_disj_formula (m_kdata # get_idata_decls ()) (m_kdata # get_ipred_decls ()) (m_kdata # get_irel_decls ()) true vars
     iform (orig_tl) in
      (cf, e)
    in
    List.map trans_one fs

   method trans_vc_ent ents=
     let d = (m_kdata # get_idata_decls ()) in
     let p = (m_kdata # get_ipred_decls ()) in
     let rels = (m_kdata # get_irel_decls ()) in
     let trans_one (ante,cons, bi, e)=
       let iante = K2C.normalize_formula d ante in
       let icons = K2C.normalize_formula d cons in
       let orig_tl =  [] in
       let vars = [] in
       let (n_tl,cante) = K2C.trans_disj_formula d p rels true vars
         iante (orig_tl) in
       let (n_tl,ccons) = K2C.trans_disj_formula d p rels true vars
         icons (n_tl) in
       {Ccmd.ante = cante;
       Ccmd.cons = ccons;
       Ccmd.expect = e;
       Ccmd.bi = bi;
       }
     in
    List.map trans_one ents

  method do_built_flow_hierachy ()=
    let () = Inode.inbuilt_build_exc_hierarchy () in (* for inbuilt control flows *)
    let () = Inode.build_exc_hierarchy true (m_kdata # get_idata_decls ()) in
    let () = exlist # compute_hierarchy  in
    let () = Inode.build_hierarchy (m_kdata # get_idata_decls ()) in
    ()

  method do_parse ()= m_kdata # do_parse_iprog ()

  method do_print_k ()= m_kdata # print_k ()

  method do_print_core ()= m_kdata # print_core ()

  method trans_prog ()=
    let cdata_declrs =
      (self # trans_data_decls (m_kdata # get_idata_decls ())) in
    let () = m_kdata # set_cdata_decls cdata_declrs in
    let tmp_preds,ls_mutrec_preds, pred_rec, pred_scc  = order_preds (m_kdata #get_ipred_decls ()) m_pred_rec m_pred_scc in
    let () = m_pred_scc <- pred_scc in
    let () = m_pred_rec <- pred_rec in
    let cpred_declrs = self # trans_pred_decls  ls_mutrec_preds
          (List.map (fun v -> (v,[])) tmp_preds) in
    let () = m_kdata # set_cpred_decls cpred_declrs in
    (* SAT *)
    let csat_queries = self # trans_vc_sat (m_kdata #get_isat_queries ()) in
    let () = m_kdata # set_csat_queries csat_queries in
    (* ENT *)
    let cent_queries = self # trans_vc_ent (m_kdata #get_ient_queries ()) in
    let () = m_kdata # set_cent_queries cent_queries in
    ()

  method do_check_sat ()=
  let _ = List.map (fun (f, oexp) ->
      let r, op = Kengine.check_sat (m_kdata#get_cpred_decls ()) f in
      let () = print_endline_quiet ("checksat " ^ (Cformula.string_of f)  ^ ".") in
      let () = print_endline ((* "\nRESULT = " ^ *) "\n" ^ (Out.string_of r) ^ "\n") in
      if !VarGen.quiet_mode then () else
      let () = match oexp with
        | None -> ()
        | Some e -> let b, msg = Out.validate e r in
          if not b then
            let () = print_endline_quiet ("Wrong Result: " ^ msg ^"\n") in
            ()
          else ()
      in
      ()
  ) (m_kdata # get_csat_queries ()) in
    ()

  method do_check_ent ()=
  let _ = List.map (fun ent ->
      let r, op = Kent.check_ent (m_kdata#get_cpred_decls ()) ent in
      let () = print_endline_quiet (Ccmd.string_of_cmd_ent ent) in
      let () = print_endline ((* "\nRESULT = " *) (Out.string_of r)) in
      if !VarGen.quiet_mode then () else
      let () = match ent.Ccmd.expect with
        | None -> ()
        | Some e -> let b, msg = Out.validate e r in
          if not b then
            let () = print_endline_quiet ("Wrong Result: " ^ msg ^"\n") in
            ()
          else ()
      in
      ()
  ) (m_kdata # get_cent_queries ()) in
    ()

end;;
