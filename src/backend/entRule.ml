open Globals
open Gen
open VarGen

module CF = Cformula
module PeN = CpredNode
module PoN = CptoNode

module CH = Cheap

module CP = Cpure

module SLND = SlNode.SL_NODE_DATA
module SLN = SlNode
module EQ = Eql

module ENT = EntNode.ENT_NODE_DATA
module E = EntNode

open Com

type frame_pto = {
    lhs_node : PoN.t;
    rhs_node: PoN.t;
    lhs_subst: Var.pair list; (* possibly empty -> no subst *)
    rhs_subst: Var.pair list; (* possibly empty -> no subst *)
    rhs_proven: CP.t option; (* added to RHS for proving *)
}

type frame_pred = {
    lhs_node : PeN.t;
    rhs_node: PeN.t;
    lhs_subst: Var.pair list; (* possibly empty -> no subst *)
    rhs_subst: Var.pair list; (* possibly empty -> no subst *)
    rhs_proven: CP.t option; (* added to RHS for proving *)
}

type ent_inf =
  | IR_FR_PTO of frame_pto
  | IR_FR_PRED of frame_pred
  | IR_LUNFOLD of (PeN.t * CF.t)
  | IR_LB_BASE_UNFOLD of (PeN.t list * CF.t)
  | IR_TW_BASE_UNFOLD of (ENT.t)
  | IR_RUNFOLD of (PeN.t * CF.t)
  | IR_RCOMPOSE of (PeN.t * PeN.t * PeN.t list)
  | IR_LCOMPOSE of (PeN.t * PeN.t * PeN.t list)
  | IR_RSTRE of (PeN.t * PeN.t * PeN.t)
  | IR_CC of (int * int * (Var.t * Var.t) list)
  | IR_SUBST of (Var.t * Var.t) list
  | IR_RINST of (Var.t * Var.t) list (*instantiate ex variables in RHS*)
  | IR_RNON_INST of PeN.t list (* reset quantifier inst flag of rhs vns *)
  | IR_AXIOM_OVER of CF.t
        (*over - approximate LHS -> false. including not(E=E) *)
  | IR_EX_MIDD of ( Var.t * Var.t * bool)
  | IR_HYPO of (SLND.t * SLND.t)
  | IR_LBase of PeN.t
  | IR_RBase of PeN.t
  | IR_EX_LHS of (Var.t * Var.t) list
  | IR_EX_EQ_RHS of (Var.t * Var.t) list
  | IR_SEQ of (ent_inf * ent_inf)

type t = ent_inf

let pr_sst sst= if sst=[] then "" else (pr_list Var.string_of_pair) sst

let string_of_frame_pto (m: frame_pto) : string=
  "lhs_node: " ^ (PoN.string_of m.lhs_node) ^"[" ^(pr_sst m.lhs_subst) ^ "]\n" ^
      "      rhs_node: " ^ (PoN.string_of m.rhs_node) ^ "[" ^ (pr_sst m.rhs_subst) ^ "]\n" ^
      "      to-be-proven: " ^ ((pr_option CP.string_of) m.rhs_proven)


let string_of_frame_pred (m: frame_pred) : string=
  "lhs_node: " ^ (PeN.string_of m.lhs_node) ^"[" ^(pr_sst m.lhs_subst) ^ "]\n" ^
      "      rhs_node: " ^ (PeN.string_of m.rhs_node) ^ "[" ^ (pr_sst m.rhs_subst) ^ "]\n" ^
      "      to-be-proven: " ^ ((pr_option CP.string_of) m.rhs_proven)

let rec string_of r= match r with
  | IR_FR_PTO m -> "Frame (pto): " ^ (string_of_frame_pto m)
  | IR_FR_PRED m -> "Frame (pred): " ^ (string_of_frame_pred m)
  | IR_LUNFOLD (vn, f) -> "LUnfold: " ^ (pr_pair PeN.string_of CF.string_of) (vn, f)
  | IR_LB_BASE_UNFOLD  (vns, f) -> "LBig Base Unfold: " ^ (pr_pair (pr_list PeN.string_of) CF.string_of) (vns, f)
  | IR_TW_BASE_UNFOLD e -> "tw base unfold: " ^ (ENT.string_of_short e)
  | IR_RUNFOLD (vn, f) -> "RUnfold: " ^ (pr_pair PeN.string_of CF.string_of) (vn, f)
  | IR_RCOMPOSE (vn, vn1, vn2s) -> "RCompose: ("  ^ (PeN.string_of vn1) ^ "*" ^ (String.concat "*" (List.map PeN.string_of vn2s)) ^ ")" ^ " <-" ^ (PeN.string_of vn)
  | IR_LCOMPOSE (vn, vn1, vn2s) -> "LCompose: (" ^  (PeN.string_of vn) ^ " ->" ^ (PeN.string_of vn1) ^ "*" ^ (String.concat "*" (List.map PeN.string_of vn2s)) ^ ")"
  | IR_RSTRE (vn, vn1, vn2) -> "RStrengthen: "  ^ (PeN.string_of vn2) ^ " <-" ^ (PeN.string_of vn1)
  | IR_CC (comp_id, bud_id, sst) -> "CC: " ^ (pr_triple string_of_int string_of_int (pr_list Var.string_of_pair)) (comp_id, bud_id, sst)
  | IR_SUBST sst -> "Subst: " ^ ((pr_list (pr_pair Var.string_of Var.string_of)) sst)
  | IR_RINST sst  -> "RInst: " ^ ((pr_list (pr_pair Var.string_of Var.string_of)) sst)
  | IR_RNON_INST vns -> "RNon Inst:" ^ ((pr_list PeN.string_of) vns)
  | IR_AXIOM_OVER f -> "Axiom_Over LHS: " ^ (CF.string_of f)
  | IR_EX_MIDD (sv1, sv2, b) ->
        let str = if b then
          (Var.string_of sv1) ^ "=" ^ (Var.string_of sv2)
        else (Var.string_of sv1) ^ "!=" ^ (Var.string_of sv2)
        in
        "Exclude Middle: (" ^ str ^ ")"
  | IR_HYPO (cons_before, cons_after) -> "HYPO (rhs) " ^ (CP.string_of (SLND.to_pure cons_before)) ^ " ==> " ^ (CP.string_of (SLND.to_pure cons_after))
  | IR_LBase vn -> "LBase "^(PeN.string_of vn)
  | IR_RBase vn -> "RBase "^(PeN.string_of vn)
  | IR_EX_LHS sst -> "Skolem Ex LHS: " ^ ((pr_list (pr_pair Var.string_of Var.string_of)) sst)
  | IR_EX_EQ_RHS sst -> "Skolem EX EQ RHS: " ^ ((pr_list (pr_pair Var.string_of Var.string_of)) sst)
  | IR_SEQ (ir1, ir2) -> "Seq:\n-  " ^ (string_of ir1) ^"\n-   "^
        (string_of ir2)

let make_frame_pto ln rn lsst rsst rproven=
  IR_FR_PTO {
    lhs_node = ln;
    rhs_node = rn;
    lhs_subst = lsst;
    rhs_subst = rsst;
    rhs_proven = rproven;
  }

let make_frame_pred ln rn lsst rsst rproven=
  IR_FR_PRED {
    lhs_node = ln;
    rhs_node = rn;
    lhs_subst = lsst;
    rhs_subst = rsst;
    rhs_proven = rproven;
  }

let is_frame_pred_wo_cond entR=
  match entR with
    | IR_FR_PRED r -> begin
        match r.rhs_proven with
          | None -> true
          | Some _ -> false
      end
    | _ -> false

let subst sst er0 =
  let rec aux er= match er with
  | IR_FR_PTO m -> IR_FR_PTO { m with lhs_node = PoN.subst sst m.lhs_node;
        rhs_node = PoN.subst sst m.rhs_node}
  | IR_FR_PRED m -> IR_FR_PRED {m with lhs_node = PeN.subst sst m.lhs_node;
        rhs_node = PeN.subst sst m.rhs_node}
  | IR_LUNFOLD (vn, f) -> IR_LUNFOLD (PeN.subst sst vn, CF.subst sst f)
  | IR_LB_BASE_UNFOLD  (vns, f) -> IR_LB_BASE_UNFOLD  (List.map (PeN.subst sst) vns, CF.subst sst f)
  | IR_TW_BASE_UNFOLD e -> IR_TW_BASE_UNFOLD {e with ENT.ante = SLND.subst sst e.ENT.ante; ENT.cons = SLND.subst sst e.ENT.cons;
    }
  | IR_RUNFOLD (vn, f) -> IR_RUNFOLD (PeN.subst sst vn, CF.subst sst f)
  | IR_RCOMPOSE (vn, vn1, vns2) -> IR_RCOMPOSE (PeN.subst sst vn, PeN.subst sst vn1, List.map (PeN.subst sst) vns2)
  | IR_LCOMPOSE (vn, vn1, vns2) -> IR_LCOMPOSE (PeN.subst sst vn, PeN.subst sst vn1, List.map (PeN.subst sst) vns2)
  | IR_RSTRE (vn, vn1, vn2) -> IR_RSTRE (PeN.subst sst vn, PeN.subst sst vn1, (PeN.subst sst) vn2)
  | IR_CC (comp_id, bud_id, sst) -> IR_CC (comp_id, bud_id, sst)
  | IR_SUBST sst1 -> IR_SUBST (List.map (fun (v1, v2) -> Var.subst sst v1, Var.subst sst v2) sst1)
  | IR_RINST sst1 -> IR_RINST (List.map (fun (v1, v2) -> Var.subst sst v1, Var.subst sst v2) sst1)
  | IR_RNON_INST vns -> IR_RNON_INST (List.map (PeN.subst sst) vns)
  | IR_AXIOM_OVER f -> IR_AXIOM_OVER (CF.subst sst f )
  | IR_EX_MIDD (sv1, sv2, b) -> IR_EX_MIDD (Var.subst sst sv1, Var.subst sst sv2, b)
  | IR_HYPO (cons1, cons2) -> IR_HYPO (SLND.subst sst cons1, SLND.subst sst cons2)
  | IR_LBase vn -> IR_LBase (PeN.subst sst vn)
  | IR_RBase vn -> IR_RBase (PeN.subst sst vn)
  | IR_EX_LHS sst1 -> IR_EX_LHS (List.map (fun (v1, v2) -> Var.subst sst v1, Var.subst sst v2) sst1)
  | IR_EX_EQ_RHS sst1 -> IR_EX_EQ_RHS (List.map (fun (v1, v2) -> Var.subst sst v1, Var.subst sst v2) sst1)
  | IR_SEQ (er1, er2) -> IR_SEQ (aux er1, aux er2)
  in aux er0

let flatten_proofs ir0 =
  let rec aux ir res= match ir with
    | IR_SEQ (er1, er2) -> let res1 = aux er1 res in
      (aux er2 res1)
    | _ -> res@[ir]
  in aux ir0 []


let ps_rhs_instantiate cpreds e sst=
  let n_rhs = SLND.subst_qvars sst e.ENT.cons in
  let () = Debug.ninfo_hprint (add_str "n_rhs" (SLND.string_of)) n_rhs no_pos in
  let n_fp = Cheap.h_subst sst e.ENT.fp in
  let n_e = {e with ENT.cons = n_rhs;
      ENT.fp = n_fp;
  } in
  [(n_e, IR_RINST sst)]

(**************************************************)
        (* FRAME POINTS-TO *)
(**************************************************)

let find_pto_match fr_lptos fr_rptos leqs reqs=
  let reqs = (leqs@reqs) in
  let rec aux lptos =
    match lptos with
      | ln::rest -> begin
          try
            let rn = List.find (fun rn ->
                let l_cl = Var.get_eq_closure leqs [ln.PoN.hpto_node] in
                let r_cl = Var.get_eq_closure reqs [rn.PoN.hpto_node] in
                Var.intersect l_cl r_cl != []) fr_rptos in
            [(ln, rn)]
          with Not_found -> aux rest
        end
      | [] -> []
  in
  aux fr_lptos

let unify_pto lqvars rqvars lvars rvars=
  let rec do_unify sst (lsst, rsst, qf)=
    match sst with
      | (v1,v2)::rest -> begin
          let lq = Var.mem v1 lqvars in
          let rq = Var.mem v2 rqvars in
          match lq, rq with
            | true, true -> let v = Var.fresh_var v1 in
              do_unify rest (lsst@[(v1,v)], rsst@[(v2,v)], qf)
            | true, false -> let v = Var.fresh_var v1 in
                  do_unify rest (lsst@[(v1,v)], rsst, qf@[(v2,v)])
            | false, true -> do_unify rest (lsst, rsst@[(v2,v1)], qf)
            | false, false -> do_unify rest (lsst, rsst, qf@[(v2,v1)])
        end
      | [] -> (lsst, rsst, qf)
  in
  do_unify (List.combine lvars rvars) ([],[],[])

let mk_eq (v1,v2) = CP.mkEqExp (Exp.mkVar v1 no_pos) (Exp.mkVar v2 no_pos) no_pos

let unfold_pred cpreds vn=
  try
    (* let pdecl = List.find (fun pd -> Ustr.str_eq vn.PeN.hpred_name pd.Cpred.pred_name) cpreds in *)
(*     let args = Var.fresh_vars pdecl.Cpred.pred_vars in *)
(*     let sst0 = List.combine pdecl.Cpred.pred_vars args in *)
(*     let pred_defn = CF.subst sst0 pdecl.Cpred.pred_formula in *)
(*     let sst = List.combine args vn.PeN.hpred_arguments in *)
(*     let () = Debug.info_hprint (add_str "pdecl.Cpred.pred_formula" (CF.string_of)) pdecl.Cpred.pred_formula no_pos in *)
(* let () = Debug.info_hprint (add_str "sst" (pr_list Var.string_of_pair)) sst no_pos in *)
    let cf = CfUtil.unfold_pred cpreds vn in
    let () = Debug.ninfo_hprint (add_str "unfold_pred cf" (CF.string_of)) cf no_pos in
    List.map (fun f -> (vn, f)) (CF.list_of_disjuncts cf)
  with Not_found -> []

let unfold_base_pred cpreds vn=
  let cf = CfUtil.unfold_pred cpreds vn in
  let () = Debug.ninfo_hprint (add_str "unfold_pred cf" (CF.string_of)) cf no_pos in
  List.map (fun f -> (vn, f)) (List.filter (CF.isEmptyHeap) (CF.list_of_disjuncts cf) )

(******************************)
  (*EX-MIDDLE*)
let check_excluded_x srcs tars lneqs=
  match srcs, tars with
    | s::_, t::_ -> begin
        if Var.equal s t then None
        else
          if List.exists (fun (sv1, sv2) ->
              (Var.equal sv1 s && Var.equal sv2 t) ||
                  (Var.equal sv2 s && Var.equal sv1 t)
          ) lneqs then
            None
          else Some (s, t)
      end
    | _ -> None

let check_excluded srcs tars lneqs=
  let pr1 = Var.string_of_list in
  let pr2 = pr_list Var.string_of_pair in
  let pr_out = pr_option Var.string_of_pair in
  Debug.no_3 "check_excluded" pr1 pr1 pr2 pr_out
      (fun _  _ _ -> check_excluded_x srcs tars lneqs)
      srcs tars lneqs

(*prune linear base*)
let aux_prune_linear_base_x cpreds f=
  let h = f.SLND.heap in
  let unfold_lbls = Cpred.search_pred_base_linear_unfold
    cpreds h.SLND.hpreds h.SLND.eql_f.EQ.eqs h.SLND.eql_f.EQ.null_vars in
  match unfold_lbls with
    | [(sub_vn, sub_br)] ->
          let n_hpreds = List.filter (fun vn1 -> not(PeN.equal vn1 sub_vn)) h.SLND.hpreds in
          let n_h = {h with SLND.hpreds = n_hpreds} in
          let sst1, n_f = SLN.mkStarAnd_f cpreds true ({f with heap = n_h}) sub_br  in
          sst1, n_f
    | _ -> [], f

let aux_prune_linear_base cpreds f=
  let pr1 = SLND.string_of in
  let pr_out = pr_pair (pr_list Var.string_of_pair) pr1 in
  Debug.no_1 "aux_prune_linear_base" pr1 pr_out
      (fun _ ->  aux_prune_linear_base_x cpreds f) f


let ps_exclude_middle cpreds (sv1,sv2) is_left vn e=
  let ante = e.ENT.ante in
  let a_h = ante.SLND.heap in
  let a_h_eql = a_h.SLND.eql_f in
  let a_h_qf_eql = a_h.SLND.qf_eql_f in
  (*sv1=sv2*)
  let cons0 = e.ENT.cons in
  let a_h_eql2 = EQ.mkAnd_eqs a_h_eql [sv1,sv2] in
  let a_h_qf_eql2 = EQ.mkAnd_eqs a_h_qf_eql [sv1,sv2] in
  let a_h2 = {a_h with SLND.eql_f = a_h_eql2;
      SLND.qf_eql_f = a_h_qf_eql2; } in
  let ante2 = {ante with SLND.heap = a_h2} in
  (* let sst, ante1 = SLN.mkStarAnd_f cpreds true ante2 br in *)
  let sst, ante21 = SLN.elim_eq ante2 in
  let cons1 = SLND.subst sst cons0 in
  let _, cons2 = aux_prune_linear_base cpreds cons1 in
  let qvars = List.map (Var.subst sst) e.ENT.qvars in
  let fp1 = CH.h_subst sst e.ENT.fp in
  let e1 = E.make_cons qvars ante21 cons2 fp1 in
  (*     e1 *)
  (*   | _ -> failwith "EntRule.ps_exclude_middle: impossible" *)
  (* in *)
  (************************)
  (*sv1 != sv2*)
  let a_h_eql1 = EQ.mkAnd_diseqs a_h_eql [sv1,sv2] in
  let a_h_qf_eql1 = EQ.mkAnd_diseqs a_h_qf_eql [sv1,sv2] in
  let a_h1 = {a_h with SLND.eql_f = a_h_eql1;
      SLND.qf_eql_f = a_h_qf_eql1; } in
  let ante1 = {ante with SLND.heap = a_h1} in
  let e2 = {e with ante = ante1} in
  let r1 = IR_EX_MIDD (sv1, sv2, true) in
  let r2 = IR_EX_MIDD (sv1, sv2, false) in
  [(e2, r2); (e1, r1)]

(*****************************)
let proof_search_match_point_to_x cpreds e (ln,rn) lqvars0 lbare rqvars0 rbare=
  let lsst, rsst, to_proven_eqs = unify_pto lqvars0 rqvars0 ln.PoN.hpto_arguments rn.PoN.hpto_arguments in
  (* subtract*)
  let n_lbare = SLND.subtract_pto lbare ln in
  let n_rbare = SLND.subtract_pto rbare rn in
  (* LHS *)
  let impl_lsst = List.filter (fun (v1, _) -> Var.mem v1 lqvars0) lsst in
  let old_qvars, impl_qvars = List.split impl_lsst in
  let nl0 = SLND.add_quantifiers (Var.diff lqvars0 old_qvars) n_lbare in
  (* footprint *)
  let nfp0 = CH.mkStarAnd e.ENT.fp (CH.PtoNode ln) no_pos in
  let nl, nfp = if lsst = [] then nl0,nfp0
  else SLND.subst lsst nl0, CH.h_subst lsst nfp0 in
  (* RHS *)
  let nr0 = SLND.add_quantifiers (Var.diff rqvars0 (List.map fst rsst)) n_rbare in
  let nr1, to_proven = if to_proven_eqs == [] then nr0, None else
    let p = List.fold_left (fun p0 (v1, v2) ->
        let eq = mk_eq (v1,v2) in
        CP.mkAnd p0 eq no_pos
    ) ( mk_eq (List.hd to_proven_eqs)) (List.tl to_proven_eqs) in
    snd (SLN.mkStarAnd_pure cpreds true nr0 p), Some p in
  let nr = if rsst = [] then nr1 else SLND.subst rsst nr1 in
  let _, nr2 = aux_prune_linear_base cpreds nr in
  let pr = make_frame_pto ln rn lsst rsst to_proven in
  let nent = EntNode.make_cons impl_qvars nl nr2 nfp in
  [(nent, pr)],impl_lsst

let proof_search_match_point_to cpreds e (ln,rn) lqvars0 lbare rqvars0 rbare=
  let pr1 = ENT.string_of in
  let pr2 = pr_list_ln (pr_pair pr1 string_of) in
  let pr3 = pr_pair PoN.string_of PoN.string_of in
  let pr4 = Var.string_of_list in
  let pr5 = SLND.string_of in
  let pr_out = pr_pair pr2 (pr_list Var.string_of_pair) in
  Debug.no_6 "ps.proof_search_match_point_to" pr1 pr3
       pr4 pr5 pr4 pr5 pr_out
      (fun _ _ _ _ _ _ -> proof_search_match_point_to_x cpreds e (ln,rn) lqvars0 lbare rqvars0 rbare)
      e (ln,rn) lqvars0 lbare rqvars0 rbare

(**************************************************)
        (* FRAME PREDs *)
(**************************************************)
let find_pred_match_x cpreds lvns (lqvars0: Var.t list) leqs leqnulls rvns rqvars0 reqs reqnulls=
  let all_eqs = (leqs@reqs) in
  let all_nulls = leqnulls@reqnulls in
  let rec eq_args pairs=
    match pairs with
      | (v1,v2)::rest ->
            let l_cl = Var.get_eq_closure leqs [v1] in
            let r_cl = Var.get_eq_closure all_eqs [v2] in
            (* v1, v2 are both quantified or equal *)
            if (List.exists (fun v22 -> List.exists (fun v11 -> Var.equal v11 v22) l_cl)  r_cl)  ||
              ((List.exists (fun v12 -> Var.equal v1 v12) lqvars0) && ( List.exists (fun v21 -> Var.equal v21 v2) rqvars0)) ||
              ( (List.exists (fun v11 -> List.exists (fun v12 -> Var.equal v11 v12) leqnulls) l_cl) &&
                  (List.exists (fun v11 -> List.exists (fun v12 -> Var.equal v11 v12) all_nulls) r_cl))
            then eq_args rest
            else (* Var.intersect l_cl leqnulls != [] && *)
                 (*    Var.intersect r_cl reqnulls != [] *)
              false
      | [] -> true
  in
  let is_ending_tar vn rest_vns=
    let _, tars = Cpred.get_root_tar_composition cpreds vn.PeN.hpred_name vn.PeN.hpred_arguments in
    List.for_all (fun vn1 ->
        let srcs = Cpred.get_root_src_composition cpreds vn1.PeN.hpred_name vn1.PeN.hpred_arguments in
        List.for_all (fun v1 ->
            List.for_all (fun v2 -> not (Var.equal v1 v2)) srcs) tars
    ) rest_vns
  in
  let rec aux lvns done_vns =
    match lvns with
      | ln::rest -> begin
            try
              let rn = List.find (fun rn ->
                  (Ustr.str_eq ln.PeN.hpred_name rn.PeN.hpred_name) &&
                      (eq_args (List.combine ln.PeN.hpred_arguments rn.PeN.hpred_arguments))
              ) rvns in
              (* acyclic or not *)
              if Cpred.is_pred_acyclic cpreds ln.PeN.hpred_name then
                [(ln, rn)], [], []
              else if is_ending_tar ln (rest@done_vns) then
                [], [], [(ln, rn)]
              else
                [],[(ln, rn)], []
            with Not_found -> aux rest (done_vns@[ln])
        end
      | [] -> [],[],[]
  in
  aux lvns []


let find_pred_match cpreds lvns (lqvars0: Var.t list) leqs leqnulls rvns rqvars0 reqs reqnulls=
  let pr1 = PeN.string_of in
  let pr2 = Var.string_of_list in
  let pr3 = pr_list Var.string_of_pair in
  let pr4 = pr_list (pr_pair pr1 pr1) in
  let pr_out = pr_triple pr4 pr4 pr4 in
  Debug.no_6 "EntRule.find_pred_match" (pr_list pr1) pr3 pr2 (pr_list pr1) pr3
      pr2 pr_out (fun  _ _ _ _ _ _ -> find_pred_match_x cpreds lvns lqvars0 leqs leqnulls
          rvns rqvars0 reqs reqnulls)
      lvns leqs leqnulls rvns reqs reqnulls

(*
  roots are matched
  the rest: RHS may be quantified
*)
let find_diff_pred_match_x cpreds lvns (lqvars0: Var.t list) leqs leqnulls rvns0 rqvars0 reqs reqnulls=
  let all_eqs = (leqs@reqs) in
  let all_nulls = leqnulls@reqnulls in
  let rec eq_args pairs=
    match pairs with
      | (v1,v2)::rest ->
            let l_cl = Var.get_eq_closure leqs [v1] in
            let r_cl = Var.get_eq_closure all_eqs [v2] in
            (* v1, v2 are both quantified or equal *)
            if (List.exists (fun v22 -> List.exists (fun v11 -> Var.equal v11 v22) l_cl)  r_cl)  ||
              ((* (List.exists (fun v12 -> Var.equal v1 v12) lqvars0) && *) ( List.exists (fun v21 -> Var.equal v21 v2) rqvars0)) ||
              ( (List.exists (fun v11 -> List.exists (fun v12 -> Var.equal v11 v12) leqnulls) l_cl) &&
                  (List.exists (fun v11 -> List.exists (fun v12 -> Var.equal v11 v12) all_nulls) r_cl))
            then eq_args rest
            else
              false
      | [] -> true
  in
  let is_ending_tar vn rest_vns=
    let _, tars = Cpred.get_root_tar_composition cpreds vn.PeN.hpred_name vn.PeN.hpred_arguments in
    List.for_all (fun vn1 ->
        let srcs = Cpred.get_root_src_composition cpreds vn1.PeN.hpred_name vn1.PeN.hpred_arguments in
        List.for_all (fun v1 ->
            List.for_all (fun v2 -> not (Var.equal v1 v2)) srcs) tars
    ) rest_vns
  in
  let rvns = List.filter (fun vn -> List.exists (fun v -> not (Var.mem v rqvars0) || (Var.mem v reqnulls)) vn.PeN.hpred_arguments) rvns0 in
  let rec aux lvns done_vns =
    match lvns with
      | ln::rest -> begin
            try
              let rn = List.find (fun rn ->
                  (not (Ustr.str_eq ln.PeN.hpred_name rn.PeN.hpred_name)) &&
                      (eq_args (List.combine ln.PeN.hpred_arguments rn.PeN.hpred_arguments))
              ) rvns in
              (* acyclic or not *)
              if Cpred.is_pred_acyclic cpreds ln.PeN.hpred_name then
                [(ln, rn)], [], []
              else if is_ending_tar ln (rest@done_vns) then
                [], [], [(ln, rn)]
              else
                [],[(ln, rn)], []
            with _ -> aux rest (done_vns@[ln])
        end
      | [] -> [],[],[]
  in
  aux lvns []

let find_diff_pred_match cpreds lvns (lqvars0: Var.t list) leqs leqnulls rvns rqvars0 reqs reqnulls=
  let pr1 = PeN.string_of in
  let pr2 = Var.string_of_list in
  let pr3 = pr_list Var.string_of_pair in
  let pr4 = pr_list (pr_pair pr1 pr1) in
  let pr_out = pr_triple pr4 pr4 pr4 in
  Debug.no_6 "EntRule.find_diff_pred_match" (pr_list pr1) pr3 pr2 (pr_list pr1) pr3
      pr2 pr_out (fun  _ _ _ _ _ _ -> find_diff_pred_match_x cpreds lvns lqvars0 leqs leqnulls
          rvns rqvars0 reqs reqnulls)
      lvns leqs leqnulls rvns reqs reqnulls


let find_pred_root_match_x cpreds find_all lvns leqs rvns reqs=
  let find_root_args vn=
    try
      let decl = List.find (fun p ->
          Ustr.str_eq vn.PeN.hpred_name p.Cpred.pred_name
      ) cpreds in
      let roots1 = match decl.Cpred.pred_composition_vars with
        | Some ((prs, _, _, _, _, _), _) -> (decl.pred_roots@(List.map fst prs))
        | None -> []
      in
      begin
        let roots2=
          let bases, _ = decl.Cpred.pred_base in
          let roots = List.fold_left (fun r f ->
              let qvars,_, ptos, br_p = CF.decompose f in
              let br_eqNulls, _, br_eqs, _, _ = CP.type_decomp br_p in
                r@(Var.diff (List.fold_left (fun r pto ->
                    r@(Var.get_eq_closure br_eqs [pto.PoN.hpto_node])
                    ) [] ptos) qvars)
          ) [] bases in
          roots
        in
        let roots = roots1@roots2 in
        if roots != [] then
          let sst = List.combine decl.Cpred.pred_vars vn.PeN.hpred_arguments in
          List.map (Var.subst sst) roots
        else []
      end
    with Not_found -> []
  in
  let rec aux rvns lvns_roots res=
    match rvns with
      | rn::rest -> begin
          let rroots0 = find_root_args rn in
          if rroots0 == [] then aux rest lvns_roots res
          else
            try
              let rroots = Var.get_eq_closure leqs rroots0 in
              let () = Debug.ninfo_hprint (add_str "rroots" (Var.string_of_list)) rroots no_pos in
              let (ln, _) = List.find (fun (_, lroots) ->
                Var.intersect lroots rroots != []
            ) lvns_roots in
            if not find_all then [(ln, rn)] else aux rest lvns_roots (res@[(ln, rn)])
          with Not_found -> aux rest lvns_roots res
        end
      | [] -> res
  in
  let lvns_roots = List.map (fun vn ->
      let roots = find_root_args vn in
      if roots = [] then (vn, [])
      else (vn, Var.get_eq_closure reqs roots)
  ) lvns in
  let () = Debug.ninfo_hprint (add_str "lvns_roots" (pr_list (pr_pair PeN.string_of Var.string_of_list))) lvns_roots no_pos in
  (* TODO: sort the RHS pred occurrences by lattice ordering *)
  aux rvns lvns_roots []

let find_pred_root_match cpreds find_all lvns leqs rvns reqs=
  let pr1 = PeN.string_of in
  let pr3 = pr_list Var.string_of_pair in
  let pr_out = pr_list (pr_pair pr1 pr1) in
  Debug.no_4 "EntRule.find_pred_root_match" (pr_list pr1) pr3 (pr_list pr1) pr3
      pr_out (fun _ _ _ _ -> find_pred_root_match_x cpreds find_all lvns leqs rvns reqs)
      lvns leqs rvns reqs

let unify_view leqs reqs lqvars rqvars lvars rvars=
  let rec do_unify sst (lsst, rsst, qf)=
    match sst with
      | (v1,v2)::rest -> begin
          let lq = Var.mem v1 lqvars in
          let rq = Var.mem v2 rqvars in
          match lq, rq with
            | true, true -> let v = Var.fresh_var v1 in
              do_unify rest (lsst@[(v1,v)], rsst@[(v2,v)], qf)
            | true, false -> let v = Var.fresh_var v1 in
                do_unify rest (lsst@[(v1,v)], rsst, qf@[(v2,v)])
            | false, true -> do_unify rest (lsst, rsst@[(v2,v1)], qf)
            | false, false -> let new_qf=
                let ls1 = Var.get_eq_closure leqs [v1] in
                let ls2 = Var.get_eq_closure leqs [v2] in
                if Var.intersect ls1 ls2 == [] then qf@[(v2,v1)]
                else qf
              in
              do_unify rest (lsst, rsst, new_qf)
        end
      | [] -> (lsst, rsst, qf)
  in
  do_unify (List.combine lvars rvars) ([],[],[])

let proof_search_match_pred_cond cpreds e (ln,rn) leqs reqs=
  let lqvars0 = e.ENT.ante.SLND.qvars in
  let rqvars0 = e.ENT.cons.SLND.qvars in
  let lsst, rsst, to_proven_eqs = unify_view leqs reqs lqvars0 rqvars0 ln.PeN.hpred_arguments rn.PeN.hpred_arguments in
  (* subtract*)
  let n_lbare = SLND.subtract_pred {e.ENT.ante with SLND.qvars = []} ln in
  let n_rbare = SLND.subtract_pred  {e.ENT.cons with SLND.qvars = []} rn in
  (* LHS *)
  let impl_lsst = List.filter (fun (v1, _) -> Var.mem v1 lqvars0) lsst in
  let old_qvars, impl_qvars = List.split impl_lsst in
  let nl0 = {n_lbare with SLND.qvars = (Var.diff lqvars0 old_qvars)} in
  (* footprint *)
  let nfp0 = CH.mkStarAnd e.ENT.fp (CH.PredNode ln) no_pos in
  let nl, nfp = if lsst = [] then nl0,nfp0
  else SLND.subst lsst nl0, CH.h_subst lsst nfp0 in
  (* RHS *)
  let nr0 = {n_rbare with SLND.qvars = (Var.diff rqvars0 (List.map fst rsst))} in
  let nr1, to_proven = if to_proven_eqs == [] then nr0, None else
    let p = List.fold_left (fun p0 (v1, v2) ->
        let eq = mk_eq (v1,v2) in
        CP.mkAnd p0 eq no_pos
    ) ( mk_eq (List.hd to_proven_eqs)) (List.tl to_proven_eqs) in
    (snd (SLN.mkStarAnd_pure cpreds true nr0 p)), Some p in
  let nr = if rsst = [] then nr1 else SLND.subst rsst nr1 in
  let pr =  make_frame_pred ln rn lsst rsst None in
  let nent = EntNode.make_cons e.EntNode.ENT_NODE_DATA.qvars nl nr nfp in
  [(nent, pr)]

let is_match_pred cpreds e=
  let lqvars0, lvns, lptos, leql, _ = SLN.star_decompose e.ENT.ante in
  let rqvars0, rvns, rptos, reql, _ = SLN.star_decompose e.ENT.cons in
  let leqNulls, _, leqs, _ = EQ.decompose leql in
  let reqNulls, _, reqs, _ = EQ.decompose reql in
  let l_nulls = Var.get_eq_closure leqs leqNulls in
  let r_nulls = Var.get_eq_closure reqs reqNulls in

  let m_acpreds, m_cpreds, m_cpreds_end = find_pred_match cpreds lvns lqvars0 leqs l_nulls rvns rqvars0 reqs r_nulls in
  if m_acpreds != [] || m_cpreds != [] || m_cpreds_end != [] then true
  else
    (* if List.length lvns == List.length rvns && *)
    (*   List.length lptos == List.length rptos && *)
    (*   List.for_all (fun lvn -> *)
    (*       List.exists (fun rvn -> *)
    (*           Ustr.str_eq lvn.PeN.hpred_name rvn.PeN.hpred_name) rvns) lvns *)
    (* then *)
    (*   let m_preds = find_pred_root_match cpreds false lvns leqs rvns reqs in *)
    (*   if m_preds == [] then false else *)
    (*     let lbare = SLN.star_compose {e.ENT.ante with SLND.qvars = []} in *)
    (*     let rbare = SLN.star_compose {e.ENT.cons with SLND.qvars = []} in *)
    (*   List.exists (fun (ln,rn) -> begin *)
    (*     if Ustr.str_eq ln.PeN.hpred_name rn.PeN.hpred_name then *)
    (*       let r = proof_search_match_pred_cond cpreds e (ln,rn) leqs  reqs in *)
    (*       match r with *)
    (*         | [(_, entR)] -> is_frame_pred_wo_cond entR *)
    (*         | _ -> false *)
    (*     else false *)
    (*   end *)
    (*   ) m_preds *)

    (* else *) false

(**************************************************)
        (* LEFT UNFOLD *)
(**************************************************)
let search_pred_with_match_alloca_x cpreds is_base lvns0 leqs r_allocas=
  let rec aux lvns= match lvns with
    | lvn::rest -> begin
        try
          let pdecl = List.find (fun pd -> Ustr.str_eq lvn.PeN.hpred_name pd.Cpred.pred_name) cpreds in
          let roots,src_tars = if not is_base then
            match pdecl.Cpred.pred_composition_vars with
              | Some ((src_tars, _, _, _, _, _), _) ->
                    (pdecl.Cpred.pred_roots@(List.map fst src_tars)),src_tars
              | None -> pdecl.Cpred.pred_roots,[]
          else
            let bases, _ = pdecl.Cpred.pred_base in
            let roots = List.fold_left (fun r f ->
                let qvars,_, ptos, _ = CF.decompose f in
                r@(Var.diff (List.map (fun pto -> pto.PoN.hpto_node) ptos) qvars)
            ) [] bases in
            roots, []
          in
          let sst = List.combine pdecl.Cpred.pred_vars lvn.PeN.hpred_arguments in
          let roots1 = Var.get_eq_closure leqs (List.map (Var.subst sst) roots) in
          let inter_roots = Var.intersect roots1 r_allocas in
          if inter_roots != [] then
            (unfold_pred cpreds lvn, src_tars)
            (* let cf = CF.subst sst pdecl.Cpred.pred_formula in *)
            (* List.map (fun f -> (lvn, f)) (CF.list_of_disjuncts cf) *)
          else aux rest
        with Not_found -> aux rest
      end
    | [] -> raise Not_found
  in
  aux lvns0

let search_pred_with_match_alloca cpreds is_base lvns0 leqs r_allocas=
  let pr1 = PeN.string_of in
  let pr2 = Var.string_of_list in
  let pr3 = pr_list Var.string_of_pair in
  let pr_out = pr_pair (pr_list (pr_pair pr1 CF.string_of))
  (pr_list Var.string_of_pair) in
  Debug.no_4 "EntRule.search_pred_with_match_alloca" string_of_bool (pr_list pr1) pr3 pr2 pr_out
      (fun _ _ _ _ -> search_pred_with_match_alloca_x cpreds is_base lvns0 leqs r_allocas)
      is_base lvns0 leqs r_allocas


(* general base case unfold *)
let search_pred_base_case cpreds vn=
  unfold_pred cpreds vn


(*
  generate children for LUNFOLD
   - substract lvn in LHS
   - starAnd new branch
similarly for RUNFOLD
*)
let proof_search_unfold ?ctx_pruning:(is_prune=true) cpreds e  is_left lneqs rneqs l_allocas l_nulls r_nulls unfold_lbls=
  let diseqs0 = lneqs@rneqs in
  let fp_hvars = ENT.get_hvars_fp e in
  let allnulls = r_nulls@l_nulls in
  let unfold_one r (vn, br)=
    (* let n_bare = CF.subtract_pred bare vn in *)
    (* let nf0 = CF.add_quantifiers qvars0 n_bare in *)
    let br1 = (CF.fresh_quantifiers br) in
    (* update unfold_num *)
    let br2 = CF.update_view_unfold_number (vn.PeN.hpred_unfold_num + 1) br1 in
    let br2n = SLN.mk_data cpreds false br2 in
    (* rule *!= for new point-to pred with fb *)
    let new_hvars = List.map (fun dn ->  dn.PoN.hpto_node) br2n.SLND.heap.SLND.hptos in
    let e,diseqs = if new_hvars == [] then e,diseqs0 else
      let n_ldiseqs = List.fold_left (fun r sv ->
          r@(List.map (fun sv1 -> (sv1, sv)) new_hvars)
      ) [] fp_hvars in
      let diseqs = diseqs0@n_ldiseqs in
      (*added n_diseqs into LHS*)
      let nante =   SLND.update_diseqs e.ENT.ante n_ldiseqs in
      {e with ENT.ante = nante},diseqs
    in
    (* check contrad *)
    if is_prune && ((List.exists (fun (v1, v2) ->
        Var.equal v1 v2) br2n.SLND.heap.eql_f.EQ.diseqs) ||
      (List.exists (fun pr1 ->
          List.exists (fun pr2 ->
              Var.equal_pair_vars pr1 pr2) diseqs
      ) br2n.SLND.heap.eql_f.EQ.eqs))
    then r else
      if is_left then
        let nf0 = SLND.subtract_pred e.ENT.ante vn in
        let nf1 = SLN.mkStarAnd br2n nf0 in
        let eqs0, nf2 = SLN.elim_eq nf1 in
        if SLND.is_unsat nf2 then r else
          let lqvars = nf1.SLND.qvars in
          let eqs = List.filter (fun (sv1, sv2) ->
              not (Var.mem sv2 lqvars) && not (Var.mem sv1 lqvars)
          ) eqs0 in
          let () = Debug.ninfo_hprint (add_str  "nf2" (SLND.string_of_short)) nf2 no_pos in
          (* let sst, nf3 = aux_prune_linear_base cpreds nf2 br2n.SLND.heap.SLND.eql_f.EQ.eqs in *)
          (* let eqs = eqs1@sst in *)
          let nent = {e with ENT.ante = nf2;
              ENT.cons = SLND.subst eqs e.ENT.cons;
              ENT.qvars = List.map (Var.subst eqs) e.ENT.qvars;
              ENT.fp = CH.h_subst eqs e.ENT.fp;
          } in
          let () = Debug.ninfo_hprint (add_str  "nent" (ENT.string_of_short)) nent no_pos in
          let nent2 = (* ENT.hypo *) nent in
          let ent3= if !VarGen.ent_explicit_big_step then
            let er1 =  IR_LUNFOLD (vn, br2) in
            let er2 = IR_HYPO (nent.ENT.cons, nent2.ENT.cons) in
            (nent2, IR_SEQ (er1, er2))
          else (nent2, IR_LUNFOLD (vn, br2))
          in r@[ent3]
      else
        let () = Debug.ninfo_hprint (add_str  "br2" (CF.string_of)) br2 no_pos in
        if List.exists (fun v1 ->
            List.exists (fun v2 ->
                Var.equal v1 v2) l_nulls) new_hvars
        then r
        else
          let r_null_vars = (Var.get_eq_closure br2n.SLND.heap.eql_f.EQ.eqs r_nulls)@br2n.SLND.heap.eql_f.EQ.null_vars in
          if List.exists (fun v1 ->
              List.exists (fun v2 ->
                  Var.equal v1 v2) l_allocas) r_null_vars then r
          else
            let nf0 = SLND.subtract_pred e.ENT.cons vn in
            (*should move arith relies on universal to LHS? *)
            let qvars0 = e.ENT.cons.SLND.qvars in
            (* let split_res = CfUtil.skolem_rhs_arith qvars0 br2 in *)
            let nent = (* match split_res with *)
              (* | None -> *)
                    let nf1 = SLN.mkStarAnd br2n nf0 in
                    let () = Debug.ninfo_hprint (add_str  "nf1" (SLND.string_of_short)) nf1 no_pos in
                    let nf2 = (snd (SLN.elim_eq nf1)) in
                    let () = Debug.ninfo_hprint (add_str  "nf2" (SLND.string_of_short)) nf2 no_pos in
                    (* let _, nf3 = aux_prune_linear_base cpreds nf2 br2n.SLND.heap.SLND.eql_f.EQ.eqs in *)
                    let nent = {e with ENT.cons = (* SLN.mk_data cpreds false *) SLND.elim_spatial_unused_qvars nf2
                    } in
                    let () = Debug.ninfo_hprint (add_str  "nent" (ENT.string_of_short)) nent no_pos in
                    nent
              (* | Some ( br3, p) -> *)
              (*       let br3n = SLN.mk_data cpreds false br3 in *)
              (*       let nf1 = SLN.mkStarAnd br3n nf0 in *)
              (*       let sln_p = SLN.mk_data_from_pure cpreds false p in *)
              (*       let nent = {e with ENT.ante = SLN.mkStarAnd e.ENT.ante sln_p ; *)
              (*           ENT.cons = (\* SLN.mk_data cpreds false *\) *)
              (*               SLND.elim_spatial_unused_qvars *)
              (*                   (snd (SLN.elim_eq nf1)) *)
              (*       } in *)
              (*       nent *)
            in
            if SLND.is_unsat nent.ENT.cons then r else
              let nent2 = ENT.hypo nent in
              let () = Debug.ninfo_hprint (add_str  "nent2" (ENT.string_of_short)) nent2 no_pos in
              let nent3 = if !VarGen.ent_explicit_big_step then
                let er1 =  IR_RUNFOLD (vn, br2) in
                let er2 = IR_HYPO (nent.ENT.cons, nent2.ENT.cons) in
                (nent2, IR_SEQ (er1, er2))
              else (nent2, IR_RUNFOLD (vn, br2))
              in r@[nent3]
  in
  List.fold_left unfold_one [] unfold_lbls

let proof_search_left_base_unfold ?ctx_pruning:(is_prune=true) cpreds e  lneqs rneqs l_allocas l_nulls r_nulls unfold_lbls=
  let diseqs0 = lneqs@rneqs in
  let fp_hvars = ENT.get_hvars_fp e in
  let allnulls = r_nulls@l_nulls in
  let unfold_one r (vns, br)=
    (* let n_bare = CF.subtract_pred bare vn in *)
    (* let nf0 = CF.add_quantifiers qvars0 n_bare in *)
    let br1 = (CF.fresh_quantifiers br) in
    (* update unfold_num *)
    let br2n = SLN.mk_data cpreds false br1 in
    (* rule *!= for new point-to pred with fb *)
    let new_hvars = List.map (fun dn ->  dn.PoN.hpto_node) br2n.SLND.heap.SLND.hptos in
    let e,diseqs = if new_hvars == [] then e,diseqs0 else
      let n_ldiseqs = List.fold_left (fun r sv ->
          r@(List.map (fun sv1 -> (sv1, sv)) new_hvars)
      ) [] fp_hvars in
      let diseqs = diseqs0@n_ldiseqs in
      (*added n_diseqs into LHS*)
      let nante =   SLND.update_diseqs e.ENT.ante n_ldiseqs in
      {e with ENT.ante = nante},diseqs
    in
    (* check contrad *)
    if is_prune && ((List.exists (fun (v1, v2) ->
        Var.equal v1 v2) br2n.SLND.heap.eql_f.EQ.diseqs) ||
      (List.exists (fun pr1 ->
          List.exists (fun pr2 ->
              Var.equal_pair_vars pr1 pr2) diseqs
      ) br2n.SLND.heap.eql_f.EQ.eqs))
    then r else
      let nf0 = List.fold_left (fun a vn -> SLND.subtract_pred a vn ) e.ENT.ante vns in
      let nf1 = SLN.mkStarAnd br2n nf0 in
      let eqs0, nf2 = SLN.elim_eq nf1 in
      if SLND.is_unsat nf2 then r else
        let lqvars = nf1.SLND.qvars in
        let eqs = List.filter (fun (sv1, sv2) ->
            not (Var.mem sv2 lqvars) && not (Var.mem sv1 lqvars)
        ) eqs0 in
        let () = Debug.ninfo_hprint (add_str  "nf2" (SLND.string_of_short)) nf2 no_pos in
        (* let sst, nf3 = aux_prune_linear_base cpreds nf2 br2n.SLND.heap.SLND.eql_f.EQ.eqs in *)
        (* let eqs = eqs1@sst in *)
        let nent = {e with ENT.ante = nf2;
            ENT.cons = SLND.subst eqs e.ENT.cons;
            ENT.qvars = List.map (Var.subst eqs) e.ENT.qvars;
            ENT.fp = CH.h_subst eqs e.ENT.fp;
        } in
        let () = Debug.ninfo_hprint (add_str  "nent" (ENT.string_of_short)) nent no_pos in
        let nent2 = (* ENT.hypo *) nent in
        let ent3= if !VarGen.ent_explicit_big_step then
          let er1 =   IR_LB_BASE_UNFOLD (vns, br1) in
          let er2 = IR_HYPO (nent.ENT.cons, nent2.ENT.cons) in
          (nent2, IR_SEQ (er1, er2))
        else (nent2, IR_LB_BASE_UNFOLD (vns, br1))
        in r@[ent3]
  in
  List.fold_left unfold_one [] unfold_lbls

(* unfold multiple predicate in sequence *)
let proof_search_unfold_seq ?ctx_pruning:(is_prune=true) cpreds e is_left lneqs rneqs l_allocas l_nulls r_nulls unfold_lbls_seq=
  match unfold_lbls_seq with
    | hd_lbls::rest ->
          List.fold_left (fun rs cur_lbls ->
              List.fold_left (fun r (cur_e, ir1) ->
                  let rs1 = proof_search_unfold ~ctx_pruning:is_prune cpreds cur_e  is_left lneqs rneqs l_allocas l_nulls r_nulls cur_lbls in
                  let rs2 =  List.map (fun (n_e, ir2) -> (n_e, IR_SEQ (ir1, ir2))) rs1 in
                  r@rs2
              ) [] rs
          ) (proof_search_unfold ~ctx_pruning:is_prune cpreds e is_left lneqs rneqs l_allocas l_nulls r_nulls hd_lbls) rest
    | [] -> []

let proof_search_composition_right_unfold cpreds e (lvn, rvn)=
  let lsrcs,ltars, lcyc_srcs,lcyc_tars, lacyc_srcs,lacyc_tars, lnsrcs,lntars, ln_ext_srcs,ln_ext_tars, ln_others = Cpred.get_all_src_tar_composition cpreds lvn.PeN.hpred_name lvn.PeN.hpred_arguments in
  let rsrcs,rtars,rcyc_srcs,rcyc_tars, racyc_srcs,racyc_tars, rnsrcs,rntars, rn_ext_srcs,rn_ext_tars, rn_others  = Cpred.get_all_src_tar_composition cpreds rvn.PeN.hpred_name rvn.PeN.hpred_arguments in
  (* let sst = List.combine rsrcs ltars in *)
  (* let nrvn = (Cheap.h_subst sst (Cheap.PredNode rvn)) in *)
  let aux_apply_one (q_avars, nrvns, narith) =
    let rhs = SLND.mkStarAnd_pred_arith (SLND.subtract_pred e.ENT.cons rvn) q_avars nrvns narith in
    let lhs = (SLND.subtract_pred e.ENT.ante lvn) in
    let nent = {e with ENT.ante = lhs;
        ENT.cons = rhs;
        ENT.fp = Cheap.mkStarAnd e.ENT.fp (Cheap.PredNode lvn) no_pos;
    } in
    (* let h_br = Cheap.mkStarAnd (Cheap.PredNode lvn) (Cheap.PredNode nrvn) no_pos in *)
    (* let br = CF.mkBase h_br (CP.mkTrue no_pos) no_pos in *)
    (nent, IR_RCOMPOSE (rvn, lvn, nrvns))
  in
  let ls_compose_rules = Cpred.get_composition_rule cpreds rvn.PeN.hpred_name lsrcs lcyc_srcs lacyc_srcs ln_ext_srcs racyc_srcs rn_ext_srcs
    ln_others
    ltars lcyc_tars lacyc_tars lntars ln_ext_tars
    rtars rcyc_tars racyc_tars rntars rn_ext_tars
    (* (Var.diff rvn.PeN.hpred_arguments (rsrcs@rtars@rcyc_srcs@rcyc_tars@racyc_srcs@racyc_tars@rnsrcs@rntars@ rn_ext_srcs@rn_ext_tars)) *)
    rn_others
  in
  List.map aux_apply_one ls_compose_rules

let proof_search_composition_left_unfold cpreds e (lvn, rvn)=
  let lsrcs,ltars, lcyc_srcs,lcyc_tars, lacyc_srcs,lacyc_tars, lnsrcs,lntars, ln_ext_srcs,ln_ext_tars, ln_others = Cpred.get_all_src_tar_composition cpreds lvn.PeN.hpred_name lvn.PeN.hpred_arguments in
  let rsrcs,rtars,rcyc_srcs,rcyc_tars, racyc_srcs,racyc_tars, rnsrcs,rntars, rn_ext_srcs,rn_ext_tars, rn_others  = Cpred.get_all_src_tar_composition cpreds rvn.PeN.hpred_name rvn.PeN.hpred_arguments in
  (* let sst = List.combine rsrcs ltars in *)
  (* let nrvn = (Cheap.h_subst sst (Cheap.PredNode rvn)) in *)
  let aux_apply_one (q_avars, nlvns, narith) =
    let lhs = SLND.mkStarAnd_pred_arith (SLND.subtract_pred e.ENT.ante lvn) q_avars nlvns narith in
    let rhs = (SLND.subtract_pred e.ENT.cons rvn) in
    let nent = {e with ENT.ante = lhs;
        ENT.cons = rhs;
        ENT.fp = Cheap.mkStarAnd e.ENT.fp (Cheap.PredNode rvn) no_pos;
    } in
    (* let h_br = Cheap.mkStarAnd (Cheap.PredNode lvn) (Cheap.PredNode nrvn) no_pos in *)
    (* let br = CF.mkBase h_br (CP.mkTrue no_pos) no_pos in *)
    (nent, IR_LCOMPOSE (lvn, rvn, nlvns))
  in
  let ls_compose_rules = Cpred.get_composition_rule cpreds lvn.PeN.hpred_name rsrcs rcyc_srcs racyc_srcs rn_ext_srcs lacyc_srcs ln_ext_srcs
    rn_others
    rtars rcyc_tars racyc_tars rntars rn_ext_tars
    ltars lcyc_tars lacyc_tars lntars ln_ext_tars
    (* (Var.diff rvn.PeN.hpred_arguments (rsrcs@rtars@rcyc_srcs@rcyc_tars@racyc_srcs@racyc_tars@rnsrcs@rntars@ rn_ext_srcs@rn_ext_tars)) *)
    ln_others
  in
  List.map aux_apply_one ls_compose_rules


let proof_search_strengthen_unfold cpreds e (lvn, rvn)=
  let aux_apply_one vn =
    let rhs = SLND.mkStarAnd_pred_arith (SLND.subtract_pred e.ENT.cons rvn) []  ([vn]) (CP.mkTrue no_pos) in
    let nent = {e with
        ENT.cons = rhs;
    } in
    (nent, IR_RSTRE (lvn, rvn, vn))
  in
  let ls_strengthen_rules = Cpred.get_strengthen_rules cpreds rvn.PeN.hpred_name rvn.PeN.hpred_arguments in
  List.map aux_apply_one ls_strengthen_rules

let proof_search_unfold_dupl_roots_x ?ctx_pruning:(is_prune=true) cpreds e is_left lneqs rneqs allocas l_nulls r_nulls fpvns fp_allocas vns0=
  let rec find_dups_aux vns=
    match vns with
      | (vn,roots)::rest ->
            let dups_vns = List.fold_left (fun r (vn, roots1) ->
                if List.exists (fun r -> Var.mem r roots1) roots
                then r@[vn]
                else r
            ) [] (rest) in
            if dups_vns == [] then
              if List.exists (fun r -> Var.mem r allocas) roots then
                [vn]
              else find_dups_aux rest
            else [vn]
      | [] -> []
  in
  (* find duplicate roots *)
  let vns_w_roots = List.map (fun vn ->
      let roots =  Cpred.get_root_src_composition cpreds vn.PeN.hpred_name vn.PeN.hpred_arguments in
      (vn, roots)
  ) vns0 in
  let dups_vns = find_dups_aux vns_w_roots in
  match dups_vns with
    | vn:: _ ->
          (* unfold it once, do not unfold multiple preds in sequence
             as the substituion in one unfolding does not apply to the following pred
          *)
          let unfold_lbls = unfold_pred cpreds vn (* dups_vns *) in
          proof_search_unfold ~ctx_pruning:is_prune cpreds e is_left lneqs rneqs allocas l_nulls r_nulls unfold_lbls
    | [] -> []

let proof_search_unfold_dupl_roots ?ctx_pruning:(is_prune=true) cpreds e is_left lneqs
      rneqs allocas l_nulls r_nulls fpvns fp_allocas vns0=
  let pr1 = pr_list PeN.string_of in
  let pr_out = pr_list_ln (pr_pair ENT.string_of_short string_of) in
  Debug.no_2 "proof_search_unfold_dupl_roots" Var.string_of_list pr1 pr_out
      (fun _ _ -> proof_search_unfold_dupl_roots_x ~ctx_pruning:is_prune cpreds e is_left
          lneqs rneqs allocas l_nulls r_nulls fpvns fp_allocas vns0) allocas vns0

(* let linear_pred_src_match cpreds lvns lptos leqs rvns reqs allocated_svs = *)
(*   if not !VarGen.ent_comp_linear_unfold then [] else *)
(*   let m_preds = find_pred_root_match cpreds true lvns leqs rvns reqs in *)
(*   (\* give higher priority for the starting pointers *\) *)
(*   let next_ptrs = List.fold_left (fun r pto -> r@pto.PoN.hpto_arguments) [] lptos in *)
(*   let m_preds = List.filter (fun (ln,_) -> *)
(*       let srcs, _ = Cpred.get_src_tar_acyclic cpreds ln.PeN.hpred_name ln.PeN.hpred_arguments in *)
(*       Var.intersect srcs next_ptrs == [] *)
(*   ) m_preds in *)
(*   match m_preds with *)
(*     | (ln,rn)::_ -> *)
(*         let () = Debug.ninfo_hprint (add_str "pred_root_match" (PeN.string_of)) ln no_pos in *)
(*         let (lvn,rvn) = begin *)
(*           (\* ls(x1,x2) |- ls(x1,x3) *)
(*              only unfold LHS  if x3|->_ or x3=null in either LHS or footprint, src *\) *)
(*           List.find (fun (ln1,rn1) -> *)
(*               let () = Debug.ninfo_hprint (add_str "ln1" (PeN.string_of)) ln1 no_pos in *)
(*               let () = Debug.ninfo_hprint (add_str "rn1" (PeN.string_of)) rn1 no_pos in *)
(*               let _, tars = Cpred.get_src_tar_acyclic cpreds rn1.PeN.hpred_name rn1.PeN.hpred_arguments in *)
(*               if List.length tars != 1 then false else *)
(*                 let () = Debug.ninfo_hprint (add_str "tars" (Var.string_of_list)) tars no_pos in *)
(*                 let () = Debug.ninfo_hprint (add_str "allocated_svs" (Var.string_of_list)) allocated_svs no_pos in *)
(*                 (\* let allocated_svs = (fp_allocas@l_allocas@l_nulls) in *\) *)
(*                 if List.exists (fun sv1 -> List.exists (fun sv2 -> Var.equal sv1 sv2)allocated_svs) tars then true *)
(*                 else *)
(*                   (\* let srcs = List.fold_left (fun r vn -> r@(extract_src cpreds vn)) [] lvns in *\) *)
(*                   (\* Var.intersect tars srcs != [] *\) *)
(*                   false *)
(*           ) m_preds *)
(*         end *)
(*         in [(lvn,rvn)] *)
(*     | [] -> [] *)

(**************************************************)
        (* BACK LINK *)
(**************************************************)
let construct_ccut_x pdecls bid cid sst e (m_bviews, m_bptos, lhs_comp_pure, rhs_comp)=
  let lhs_bud = e.ENT.ante in
  (* substract matched *)
  let lhs_bud1 = List.fold_left (fun f vn ->
      SLND.subtract_pred f vn
  ) lhs_bud m_bviews in
  let lhs_bud2 = List.fold_left (fun f pn ->
      SLND.subtract_pto f pn
  ) lhs_bud1 m_bptos in
  (* conjoin rhs comp *)
  (* fresh qvars of rhs_comp *)
  let rhs_comp1 = SLND.fresh_quantifiers rhs_comp in
  (* increase unfolding number *)
  let rhs_comp2 = SLND.increase_view_unfold_number rhs_comp1 in
  (* strengthen rhs_comps with lhs pure: more complete*)
  let lhs_comp_pure1 = CP.subst_var sst lhs_comp_pure in
  let () = Debug.ninfo_hprint (add_str  "lhs_comp_pure1"
 (CP.string_of)) lhs_comp_pure1 no_pos in
  (* TODO: remove redundant in lhs of bud before combined *)
  let _, rhs_comp3 = SLN.mkStarAnd_pure pdecls false rhs_comp2 lhs_comp_pure1 in
  let nf1 = SLN.mkStarAnd lhs_bud2 rhs_comp3 in
  (* new footprint *)
  let fp1 = List.fold_left (fun h vn ->
      Cheap.mkStarAnd h (Cheap.PredNode vn) no_pos
  ) e.ENT.fp m_bviews in
  let fp2 = List.fold_left (fun h pn ->
      Cheap.mkStarAnd h (Cheap.PtoNode pn) no_pos
  ) e.ENT.fp (* fp1 *)  m_bptos in
  (*use view as a back link make the sytem unsound
    (before it is not in NF(not use EX-MID for efficiency)) e.g.,
    lss-vc01: ls(x1,x2) * ls(x2,x3) |= ls(x1, x3) *)
  let nf2 = SLND.update_star_new_nodes nf1 (List.map (fun dn->
      dn.PoN.hpto_node) m_bptos) in
  (* new leaf *)
  let nent = {e with ENT.ante = nf1;
      ENT.fp = fp2;
  } in
      [(nent, IR_CC (bid,cid, sst))]

let construct_ccut pdecls bid cid sst e (m_bviews, m_bptos, lhs_comp_pure, rhs_comp)=
  let pr1 = pr_list PeN.string_of in
  let pr2 = pr_list PoN.string_of in
  let pr3 = ENT.string_of_short in
  let pr_out = pr_list_ln (pr_pair pr3 string_of) in
  let pr4 = pr_list Var.string_of_pair in
  Debug.no_3 "construct_ccut" pr4 pr3 (pr_quad pr1 pr2 CP.string_of SLND.string_of_short) pr_out
      (fun _ _ _ -> construct_ccut_x pdecls bid cid sst e (m_bviews, m_bptos, lhs_comp_pure, rhs_comp))
      sst e (m_bviews, m_bptos, lhs_comp_pure, rhs_comp)



(*This function is obsollet as it is covered by
 proof_search_unfold*)
(* whether it is base or rec *)
let proof_search_right_linear_unfold_filter_x rbrs lneqs(* l_allocas l_nulls *)= (* List.map (fun r -> [r]) rbrs *)
  match rbrs with
    | [] -> [[]]
    | [x] -> [[x]]
    | x::_ ->
          let brs = List.fold_left (fun r ((_, ef) as br) -> begin
            match ef with
              | IR_RUNFOLD (_, f) ->
                    (* filter for linear fragment for more efficient *)
                    let _, _, ptos, p = CF.decompose f in
                    let eqNulls0, _, eqs, neqs, _ = CP.type_decomp p in
                    if List.exists (fun (v1, v2) -> Var.equal v1 v2) neqs then
                      let () = Debug.ninfo_hprint (add_str "xxxx" (pr_id)) "1" no_pos in
                      r
                    else
                      let allocas = Var.get_eq_closure eqs (List.map (fun n -> n.PoN.hpto_node) ptos) in
                      let eqNulls = Var.get_eq_closure eqs eqNulls0 in
                      (* if (l_allocas == [] && allocas == [] && eqNulls == [] && l_nulls==[] ) *)
                      (*   || (Var.intersect l_allocas allocas != []) || *)
                      (*   (Var.intersect eqNulls l_nulls != []) then *)
                      (*     (r@[[br]]) *)
                      (* else r *)
                      if List.exists (fun pr1 ->
                          List.exists (fun pr2 -> Var.equal_pair_vars pr1 pr2) lneqs ) eqs then
                        let () = Debug.ninfo_hprint (add_str "xxxx" (pr_id)) "2" no_pos in
                        r
                      else
                        (r@[[br]])
              | _ -> (r@[[br]])
          end
          ) [] rbrs in
          (* if List.length brs == 0 then *)
          (*   [[x]] *)
          (* else *) brs

let proof_search_right_linear_unfold_filter rbrs lneqs (* l_allocas l_nulls *)=
  let pr1 = ENT.string_of_short in
  let pr2 = pr_list_ln (pr_pair pr1 string_of) in
  let pr3 = pr_list Var.string_of_pair in
  Debug.no_2 "proof_search_right_linear_unfold_filter"
      pr2 pr3 (pr_list_ln pr2)
      (fun _ _ -> proof_search_right_linear_unfold_filter_x rbrs lneqs) rbrs lneqs (* l_allocas l_nulls *)

let proof_search_left_unfold_pred_x cpreds e lvn leqs lneqs rneqs l_allocas l_nulls r_nulls=
  let lunfold_lbls = unfold_pred cpreds lvn in
  let r =  proof_search_unfold cpreds e true lneqs rneqs l_allocas l_nulls r_nulls lunfold_lbls in
  let status = if r==[] then ELuEmp else ENorm in
  ([r], [], status)

let proof_search_left_unfold_pred cpreds e lvn leqs lneqs rneqs l_allocas l_nulls r_nulls=
  let pr1 = ENT.string_of_short in
  let pr2 = PeN.string_of in
  let pr3 = pr_list Var.string_of_pair in
  let pr4 = pr_list_ln (pr_list_ln (pr_pair pr1 string_of)) in
  let pr_out = pr_triple pr4 pr3 Com.string_of_entstuck in
  Debug.no_3 "proof_search_left_unfold_pred" pr1 pr2 pr3 pr_out
      (fun _ _ _ -> proof_search_left_unfold_pred_x cpreds e lvn leqs lneqs rneqs l_allocas l_nulls r_nulls)
      e lvn leqs
