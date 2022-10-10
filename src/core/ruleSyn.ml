
open Globals
open Gen.Basic
open VarGen
open Gen

module CF = Cformula
module CH = Cheap
module CP = Cpure
module PeN = CpredNode
module V = Var
module CoRule = CcoRule

open CcoRule


let get_arith f =
  let qvars3, bare_p = CP.split_quantifiers f in
  let () = Debug.ninfo_hprint (add_str "bare_p" ((CP.string_of))) bare_p no_pos in
  let ps = CP.split_conjunctions bare_p in
  let ps_ar = List.filter (fun p -> List.for_all (fun sv -> not (Var.is_node sv)) (CP.fv p)) ps in
  let bare_p_ar = CP.join_conjunctions ps_ar no_pos in
  let qvars4 = Var.intersect qvars3 (CP.fv bare_p_ar) in
  let () = Debug.ninfo_hprint (add_str "qvars4" (pr_list (Var.string_of))) qvars4 no_pos in
  let f_arth = CP.add_quantifiers qvars4 bare_p_ar in
  f_arth

(* same starting
 generate a composition lemma
 - acylic root
 exact segment lemma
   FRAME (x1, c1, ext_c1, nonlocal_prec_c1, nonlocal_ext_c1, x2, c2, ext_c2, nonlocal_prec_c2, nonlocal_ext_c2) *
    REM1 (x2, c2, ext_c2, nonlocal_prec_c2, nonlocal_ext_c2, x3, c3, ext_c3, nonlocal_prec_c3, nonlocal_ext_c3)
     <- (x1, c1, ext_c1, nonlocal_prec_c1, nonlocal_ext_c1, x3, c3, ext_c3, nonlocal_prec_c3, nonlocal_ext_c3)
 - cyclic root
  ex ext_c2', nonlocal_ext_c2':
   FRAME (x1, c1, ext_c1, nonlocal_prec_c1, nonlocal_ext_c1, x2, c2, ext_c2, nonlocal_prec_c2, nonlocal_ext_c2) *
   REM2    (x2, c2, ext_c2', nonlocal_prec_c2,  nonlocal_ext_c2', x2, c2, ext_c2, nonlocal_precise2, nonlocal_prec_c2, nonlocal_ext_c2) *
   REM1     (x2, c2, ext_c2, nonlocal_prec_c2, nonlocal_ext_c2, x3, c3, ext_c3, nonlocal_prec_c3, nonlocal_ext_c3)
     <- (x1, c1, ext_c1, nonlocal_prec_c1, nonlocal_ext_c1, x3, c3, ext_c3, nonlocal_prec_c3, nonlocal_ext_c3)

extend from the right of the second extensiable properties
   ex ext_c2', nonlocal_ext_c2':
   FRAME (x1, c1, ext_c1, nonlocal_prec_c1, nonlocal_ext_c1, x2, c2, ext_c2, nonlocal_prec_c2, nonlocal_ext_c2) *
   REM1_ext-r     (x2, c2, ext_c2', nonlocal_prec_c2, nonlocal_ext_c2', x3, c3, ext_c3, nonlocal_prec_c3, nonlocal_ext_c3) /\ invariant
   of (c2, ext_c2, nonlocal_prec_c2, nonlocal_ext_c2, c2, ext_c2', nonlocal_prec_c2, nonlocal_ext_c2')
     <- (x1, c1, ext_c1, nonlocal_prec_c1, nonlocal_ext_c1, x3, c3, ext_c3, nonlocal_prec_c3, nonlocal_ext_c3)

*)

(* diff starting
    REM4 (x1, c1, ext_c1', nonlocal_prec_c1, nonlocal_ext_c1',  x1, c1, ext_c1, nonlocal_prec_c1, nonlocal_ext_c1)
   FRAME  (x1, c1, ext_c1, nonlocal_prec_c1, nonlocal_ext_c1, x2, c2, ext_c2, nonlocal_prec_c2, nonlocal_ext_c2) *
   REM1  (x2, c2, ext_c2, nonlocal_prec_c2, nonlocal_ext_c2, x3, c3, ext_c3, nonlocal_prec_c3, nonlocal_ext_c3) *
    <- (x1, c1, ext_c1', nonlocal_prec_c1, nonlocal_ext_c1', x3, c3, ext_c3, nonlocal_prec_c3, nonlocal_ext_c3)

*)
let generate_composable_rule cpreds pred_name pred_args0 pred_inv0 is_root_acyclic
      root_arg_prs0 local_precise_prs0 local_ext_prs0 nlocal_precise_prs0 nlocal_ext_prs0=
  if !VarGen.ent_composition_rule then begin
    (* fresh all variables names *)
    let pred_args, sst0 = List.fold_left (fun (r1, r2) v ->
        let n_v = Var.fresh_var v in
        (r1@[n_v], r2@[(v, n_v)])
    ) ([],[]) pred_args0 in
    let fresh_lst_pr_vars = List.map (fun (v1, v2) -> (Var.subst sst0 v1, Var.subst sst0 v2)) in
    let pred_inv = CP.subst_var sst0 pred_inv0 in
    let root_arg_prs = fresh_lst_pr_vars root_arg_prs0 in
    let local_precise_prs = fresh_lst_pr_vars local_precise_prs0 in
    let local_ext_prs = fresh_lst_pr_vars local_ext_prs0 in
    let nlocal_precise_prs = fresh_lst_pr_vars nlocal_precise_prs0 in
    let nlocal_ext_prs = fresh_lst_pr_vars nlocal_ext_prs0 in
    let () = Debug.ninfo_hprint (add_str "root_arg_prs" (pr_list (Var.string_of_pair))) root_arg_prs no_pos in
    let () = Debug.ninfo_hprint (add_str "local_precise_prs" (pr_list (Var.string_of_pair))) local_precise_prs no_pos in
    let () = Debug.ninfo_hprint (add_str "local_ext_prs" (pr_list (Var.string_of_pair))) local_ext_prs no_pos in
    let root_src_args, root_tar_args = List.split root_arg_prs in
    let local_precise_src_args, local_precise_tar_args = List.split local_precise_prs in
    let local_ext_src_args, local_ext_tar_args = List.split local_ext_prs in
    let nl_precise_src_args, nl_precise_tar_args = List.split nlocal_precise_prs in
    let nl_ext_src_args, nl_ext_tar_args = List.split nlocal_ext_prs in
    (* other arguments *)
    let other_args = V.diff pred_args (root_src_args@local_precise_src_args@root_tar_args@local_precise_tar_args@
         local_ext_src_args@nl_precise_src_args@local_ext_tar_args@nl_precise_tar_args@nl_ext_src_args@nl_ext_tar_args) in
    (* generate cut args *)
    let root_snd_args= List.fold_left (fun (r3) (src, tar) ->
        let cut_arg = V.fresh_var tar in
        (r3@[cut_arg])
    ) ( []) (root_arg_prs) in

    let local_precise_snd_args= List.fold_left (fun (r3) (src, tar) ->
        let cut_arg = V.fresh_var tar in
        (r3@[cut_arg])
    ) ( []) (local_precise_prs) in

    let local_ext_snd_args, local_ext_sndp_args= List.fold_left (fun ( r3,r4) (src, tar) ->
        let cut_arg = V.fresh_var tar in
        let cutp_arg = V.fresh_var tar in
        ( r3@[cut_arg], r4@[cutp_arg])
    ) ([], []) (local_ext_prs) in

    let nl_precise_snd_args= List.fold_left (fun ( r3) (src, tar) ->
        let cut_arg = V.fresh_var tar in
        (* let cutp_arg = V.fresh_var tar in *)
        (r3@[cut_arg](* , r4@[cutp_arg] *))
    ) ([]) (nlocal_precise_prs) in
    let nl_ext_snd_args, nl_ext_sndp_args= List.fold_left (fun (r3, r4) (src, tar) ->
        let cut_arg = V.fresh_var tar in
        let cutp_arg = V.fresh_var tar in
        ( r3@[cut_arg] , r4@[cutp_arg])
    ) ([], []) (nlocal_ext_prs) in

    let p_same_coRule, frame_other, frame_sst_other, snd_other, snd_sst_other = match other_args with
      | [x] -> if Var.is_node x then (CP.mkTrue no_pos), [], [], [], [] else
          let frame_sv = V.fresh_var x in
          let snd_sv = V.fresh_var x in
          let rhs = Exp.Add ((Exp.mkVar frame_sv no_pos), (Exp.mkVar snd_sv no_pos), no_pos) in
          let p = Cpure.mkEqExp (Exp.mkVar x no_pos) rhs no_pos in
          p, [frame_sv], [(x, frame_sv)], [snd_sv], [(x, snd_sv)]
      | _ -> (CP.mkTrue no_pos), [], [], [], []
    in
    let cut_args = (root_snd_args@local_precise_snd_args@local_ext_snd_args@nl_precise_snd_args@nl_ext_snd_args) in
    let () = Debug.ninfo_hprint (add_str "cut_args" (pr_list (Var.string_of))) cut_args no_pos in
    let () = Debug.ninfo_hprint (add_str "local_precise_tar_args" (pr_list (Var.string_of))) local_precise_tar_args no_pos in
    (*first segment: FRAME*)
    let sst10 = List.combine (root_tar_args@local_precise_tar_args@local_ext_tar_args@nl_precise_tar_args@nl_ext_tar_args) cut_args in
    let sst1 = sst10@frame_sst_other in
    let () = Debug.ninfo_hprint (add_str "sst1" (pr_list (Var.string_of_pair))) sst1 no_pos in
    let fst_args = List.map (V.subst sst1) pred_args in
    let fst_vn = PeN.mk pred_name false fst_args no_pos in
    let () = Debug.ninfo_hprint (add_str "fst_vn" (PeN.string_of)) fst_vn no_pos in
    (*second segment: REM1*)
    let sst20 = List.combine (root_src_args@local_precise_src_args@ local_ext_src_args@nl_precise_src_args@nl_ext_src_args) cut_args in
    let sst2 = sst20@snd_sst_other in
    let snd_args = List.map (V.subst sst2) pred_args in
    let snd_vn = PeN.mk pred_name false snd_args no_pos in
    let same_coRules =
      (* full composition or not *)
      if is_root_acyclic || (local_ext_prs==[] &&  nlocal_ext_prs==[]) then
        let same_coRule = mk root_src_args local_precise_src_args
          local_ext_src_args nl_ext_src_args
          local_ext_src_args nl_ext_src_args
          frame_other
          root_snd_args local_precise_snd_args local_ext_snd_args nl_precise_snd_args nl_ext_snd_args
          root_tar_args local_precise_tar_args local_ext_tar_args nl_precise_tar_args nl_ext_tar_args
          other_args
          snd_other fst_vn [snd_vn] p_same_coRule in
        [same_coRule]
      else
       (*third segment: REM2*)
        let sst3 = List.combine (root_src_args@local_precise_src_args@nl_precise_src_args@local_ext_src_args@nl_ext_src_args) (root_snd_args@local_precise_snd_args@nl_precise_snd_args@local_ext_sndp_args@nl_ext_sndp_args) in
        let snd_args2 = List.map (V.subst (sst3@sst1)) pred_args in
        let snd_vn2 = PeN.mk pred_name false snd_args2 no_pos in
        (*NO: gen relational assumptions: lemma proving *)
        (* TEMPORAL *)
        (* List.fold_left (fun r (sv1, sv2) -> *)
        (*     let p = Cpure.mkEqVar sv1 sv2 no_pos in *)
        (*     Cpure.mkAnd r p no_pos *)
        (* ) (CP.mkTrue no_pos) (List.combine qvar_cut_args cut_non_args) *)
        (* complete -> YES: find pure *)
        let same_coRule = mk root_src_args local_precise_src_args
          local_ext_src_args nl_ext_src_args
          local_ext_src_args nl_ext_src_args
          []
          root_snd_args local_precise_snd_args local_ext_snd_args nl_precise_snd_args nl_ext_snd_args
          root_tar_args local_precise_tar_args local_ext_tar_args nl_precise_tar_args nl_ext_tar_args
          other_args
          (local_ext_sndp_args@nl_ext_sndp_args) fst_vn [snd_vn;snd_vn2] (CP.mkTrue no_pos) in
        let same_emp_corules = if local_ext_prs == [] && nlocal_ext_prs==[] then [] else
          let sst_src_extr = List.combine (root_src_args@local_precise_src_args@local_ext_src_args@nl_precise_src_args@nl_ext_src_args)
            (root_snd_args@local_precise_snd_args@local_ext_sndp_args@nl_precise_snd_args@nl_ext_sndp_args)
          in
          let snd_vn_args_ext_r = List.map (V.subst sst_src_extr) pred_args in
          let snd_vn_ext_r = PeN.mk pred_name false snd_vn_args_ext_r no_pos in
          let inv_snd_vn2 = CP.subst_var (List.combine pred_args snd_args2) pred_inv in
          let sst_ext_src = List.combine (root_src_args@local_precise_src_args@local_ext_src_args@nl_precise_src_args@nl_ext_src_args)
            cut_args in
          let sst_ext_tar = List.combine (root_tar_args@local_precise_tar_args@local_ext_tar_args@nl_precise_tar_args@nl_ext_tar_args)
              (root_snd_args@local_precise_snd_args@local_ext_sndp_args@nl_precise_snd_args@nl_ext_sndp_args) in
          let inv_snd_vn2_extr_arith = get_arith (CP.subst_var (sst_ext_src@sst_ext_tar)  pred_inv) in
          let same_emp_lemma = mk root_src_args local_precise_src_args
            local_ext_src_args nl_ext_src_args
            local_ext_src_args nl_ext_src_args
            []
            root_snd_args local_precise_snd_args local_ext_snd_args nl_precise_snd_args nl_ext_snd_args
            root_tar_args local_precise_tar_args local_ext_tar_args nl_precise_tar_args nl_ext_tar_args
            other_args
            (local_ext_sndp_args@nl_ext_sndp_args) fst_vn [snd_vn_ext_r] (inv_snd_vn2_extr_arith) in
          [same_emp_lemma]
        in
        same_emp_corules@[same_coRule]
    in
    (* diff starting point *)
    let diff_rules = if local_ext_prs == []  && nlocal_ext_prs==[] then [] else
      let sst4 = List.combine (local_ext_src_args@nl_ext_src_args ) (local_ext_sndp_args@nl_ext_sndp_args) in
      let sst5 = List.combine (root_tar_args@local_precise_tar_args@local_ext_tar_args@nl_precise_tar_args@nl_ext_tar_args) (root_src_args@local_precise_src_args@local_ext_src_args@nl_precise_src_args@nl_ext_src_args) in
      let snd_args3 = List.map (V.subst (sst4@sst5)) pred_args in
      let snd_vn3 = PeN.mk pred_name false snd_args3 no_pos in
      let diff_coRule = mk root_src_args local_precise_src_args
        local_ext_sndp_args nl_ext_sndp_args
        local_ext_src_args nl_ext_src_args
        []
        root_snd_args local_precise_snd_args local_ext_snd_args nl_precise_snd_args nl_ext_snd_args
        root_tar_args local_precise_tar_args local_ext_tar_args nl_precise_tar_args nl_ext_tar_args
        other_args
        (local_ext_sndp_args@nl_ext_sndp_args) fst_vn [snd_vn;snd_vn3] (CP.mkTrue no_pos) in
      (* if precise pure properties == [], generate lemma such that snd_vn3 == pure inv(without heap) *)
      let diff_emp =
        let inv_snd_vn3 = CP.subst_var (List.combine pred_args snd_args3) pred_inv in
        let inv_snd_vn3_arth = get_arith inv_snd_vn3 in
        let () = Debug.ninfo_hprint (add_str "inv_snd_vn3_arth" ((CP.string_of))) inv_snd_vn3_arth no_pos in
        let emp_rule = mk root_src_args local_precise_src_args
          local_ext_sndp_args nl_ext_sndp_args
          local_ext_src_args nl_ext_src_args
          []
          root_snd_args local_precise_snd_args local_ext_snd_args nl_precise_snd_args nl_ext_snd_args
          root_tar_args local_precise_tar_args local_ext_tar_args nl_precise_tar_args nl_ext_tar_args
          other_args
          (local_ext_sndp_args@nl_ext_sndp_args) fst_vn [snd_vn] inv_snd_vn3_arth in
        [(* emp_rule *)]
      in
      diff_emp@[diff_coRule]
    in
    same_coRules, diff_rules
  end
  else
    [], []

let generate_strengthen_rules_x cpreds p=
  (* let is_two = (List.length cpreds) == 2 in *)
  let fr_args = List.map Var.fresh_var p.Cpred.pred_vars in
  let mk_ent lhs_h rhs_h=
    let ante = CF.mkBase lhs_h (CP.mkTrue no_pos) no_pos in
    let cons = CF.mkBase rhs_h (CP.mkTrue no_pos) no_pos in
    {Ccmd.ante = ante;
       Ccmd.cons = cons;
       Ccmd.expect = None;
       Ccmd.bi = false;
       }
  in
  let aux r p1=
    let is_same_card = List.length p.Cpred.pred_vars == List.length p1.Cpred.pred_vars in
    if (not (Ustr.str_eq p.Cpred.pred_name p1.Cpred.pred_name)) &&
      ((is_same_card)
        (* || is_two *)
      )
    then
      (* let lhs, rhs = if not is_same_card then *)
      (*   let rhs = PeN.mk ~un:0 ~us:0 ~ut:1 p.Cpred.pred_name false p.Cpred.pred_vars no_pos in *)
      (*   let lhs = PeN.mk ~un:0 ~us:0 ~ut:1 p1.Cpred.pred_name false p1.Cpred.pred_vars no_pos in *)
      (*   (lhs, rhs) *)
      (* else *)
        let rhs = PeN.mk ~un:0 ~us:0 ~ut:1 p.Cpred.pred_name false fr_args no_pos in
        let lhs = PeN.mk ~un:0 ~us:0 ~ut:1 p1.Cpred.pred_name false fr_args no_pos in
        (* (lhs, rhs) *)
      (* in *)
      let ent = mk_ent (CH.PredNode lhs) (CH.PredNode rhs) in
      let r_entl, _ = Kent.check_ent cpreds ent in
      if r_entl == Out.VALID then
        let srule = StreRule.mk fr_args lhs in
        r@[srule]
      else r
    else r
  in
  List.fold_left aux [] cpreds

let generate_strengthen_rules cpreds p=
  let pr1 = Cpred.string_of in
  let pr2 = pr_list_ln pr1 in
  let pr_out = pr_list_ln StreRule.string_of in
  Debug.no_2 "generate_strengthen_rules" pr1 pr2 pr_out
      (fun _ _ -> generate_strengthen_rules_x cpreds p) p cpreds
