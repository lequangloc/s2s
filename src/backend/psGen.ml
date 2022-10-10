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
open EntRule



(**************************************************)
        (* FRAME POINTS-TO *)
(**************************************************)

(******************************)

(*****************************)

(**************************************************)
        (* FRAME PREDs *)
(**************************************************)
let find_pred_match_rev cpreds lvns leqs rvns reqs=
  let find_rev_args vn=
    try
      let decl = List.find (fun p ->
          Ustr.str_eq vn.PeN.hpred_name p.Cpred.pred_name
      ) cpreds in
      let tars = decl.Cpred.pred_bw_tars in
      if tars == [] then []
      else
        let sst = List.combine decl.Cpred.pred_vars vn.PeN.hpred_arguments in
        List.map (Var.subst sst) tars
    with Not_found -> []
  in
  let rec aux lvns rvns_roots=
    match lvns with
      | ln::rest -> begin
          let lroots0 = find_rev_args ln in
          if lroots0 == [] then aux rest rvns_roots
          else
            try
              let lroots = Var.get_eq_closure leqs lroots0 in
              let (rn, _) = List.find (fun (_, rroots) ->
                  Var.intersect lroots rroots != []
              ) rvns_roots in
              [(ln, rn)]
            with Not_found -> aux rest rvns_roots
        end
      | [] -> []
  in
  let rvns_revs = List.map (fun vn ->
      let revs = find_rev_args vn in
      if revs = [] then (vn, [])
      else (vn, Var.get_eq_closure reqs revs)
  ) rvns in
  (* TODO: sort the RHS pred occurrences by lattice ordering *)
  aux lvns rvns_revs


(**************************************************)
        (* LEFT UNFOLD *)
(**************************************************)

let search_ctx_unfold_x cpreds vns p eqNulls eqs neqs ptos=
  let is_ctx_implied ctx_ps p=
    (* if CP.isTrue p then true else *)
      match p with
        | CP.BForm (Term.Eq (Exp.Var(sv1, _) ,Exp.Var(sv2, _) ,_)) ->
              if Var.equal sv1 sv2 then true
              else List.exists (CP.equal p) ctx_ps
        | _ -> List.exists (CP.equal p) ctx_ps
  in
  let search_aux vn ctx_ps=
    try
      let pdecl = List.find (fun pd -> Ustr.str_eq vn.PeN.hpred_name pd.Cpred.pred_name) cpreds in
      let sst = List.combine pdecl.Cpred.pred_vars vn.PeN.hpred_arguments in
      let (_, f) = List.find (fun (br_p, br_f) ->
          let () = Debug.ninfo_hprint (add_str "br_p" (CP.string_of)) br_p no_pos in
          let br_p1 = CP.subst_var sst br_p in
          let () = Debug.ninfo_hprint (add_str "br_p1" (CP.string_of)) br_p1 no_pos in
          if not (CP.isTrue br_p) && (CP.isTrue br_p1) then true
          else
            let ps = CP.split_conjunctions br_p1 in
            let () = Debug.ninfo_hprint (add_str "ps" (pr_list CP.string_of)) ps no_pos in
            List.for_all (is_ctx_implied ctx_ps) ps
      ) pdecl.Cpred.pred_formula_w_ctx in
      let f1 = CF.subst sst f in
      [(vn, f1)]
    with Not_found -> []
  in
  let ctx_ps = CP.split_conjunctions p in
  List.fold_left (fun r vn ->
      let brs = search_aux vn ctx_ps in
      if brs == [] then r
      else r@[brs]
  ) [] vns

let search_ctx_unfold cpreds vns p eqNulls eqs neqs ptos=
  let pr1 = PeN.string_of in
  let pr_out = pr_list (pr_list (pr_pair pr1 CF.string_of)) in
  Debug.no_1 "search_ctx_unfold" (pr_list pr1) pr_out
      (fun _ -> search_ctx_unfold_x cpreds vns p eqNulls eqs neqs ptos) vns

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
        (* MAIN ALGO *)
(**************************************************)
let proof_search_try_unfold_pred_pred cpreds e (ln, rn) lbare lptos lqvars0
      rbare rptos rqvars0 lneqs rneqs l_allocas l_nulls r_nulls=
  if (List.length lptos) <= (List.length rptos) then
    (* unfold lhs *)
    let lunfold_lbls = unfold_pred cpreds ln in
    if lunfold_lbls == [] then []
    else
      let r = proof_search_unfold cpreds e true lneqs rneqs l_allocas l_nulls r_nulls lunfold_lbls in
      [r]
  else (* unfold lhs *)
    let runfold_lbls = unfold_pred cpreds rn in
    if runfold_lbls == [] then []
    else
      let rbrs = proof_search_unfold cpreds e false lneqs rneqs l_allocas l_nulls r_nulls runfold_lbls in
      List.map (fun br -> [br]) rbrs

let proof_search_try_match_pred_pred cpreds e (ln, rn)
      leqs reqs=
  let r = proof_search_match_pred_cond cpreds e (ln,rn)
    leqs reqs in
  r

let proof_search_right_unfold_pto_pred cpreds e rvns reqs l_allocas rqvars0 rbare lneqs rneqs l_allocas l_nulls r_nulls=
  let runfold_lbls, _ = search_pred_with_match_alloca cpreds true rvns reqs l_allocas in
  let rbrs =  proof_search_unfold cpreds e false lneqs rneqs l_allocas l_nulls r_nulls runfold_lbls in
  (* to clone mutiple trees *)
  let searches0 = List.map (fun br -> [br]) rbrs in
  searches0

let proof_search_right_unfold_pred cpreds e is_filter (l_allocas) rvns reqs  rqvars0 rbare lneqs rneqs l_allocas l_nulls r_nulls=
let searches0 = proof_search_right_unfold_pto_pred cpreds e rvns reqs (l_allocas) rqvars0 rbare lneqs rneqs l_allocas l_nulls r_nulls in
if searches0 == [] then []
else
  (* remove the one with the same rvn name
     as it may not terminate *)
  let searches1 = if is_filter then
    List.filter (fun ls ->
        List.for_all (fun (_, r) ->
            match r with
              | IR_RUNFOLD (vn, f) -> let vns, _ = CF.star_decompose f in
                List.for_all (fun vn2 -> not (Ustr.str_eq vn.PeN.hpred_name vn2.PeN.hpred_name) ) vns
              | _ -> false
        ) ls
    ) searches0
  else (List.rev searches0)
  in searches1

let proof_search_x cpreds is_ho  e =
  let _,lbare = SLND.split_quantifiers e.ENT.ante in
  let _, rbare = SLND.split_quantifiers e.ENT.cons in
  let lqvars0, lvns, lptos, leql,_ = SLN.star_decompose e.ENT.ante in
  let rqvars0, rvns, rptos, reql,_ = SLN.star_decompose e.ENT.cons in
  let lp = SLND.to_pure e.ENT.ante in
  let rp = SLND.to_pure e.ENT.cons in
  let leqNulls, _, leqs, lneqs = (* CP.type_decomp lp *) EQ.decompose leql in
  let reqNulls, _, reqs, rneqs = (* CP.type_decomp rp *) EQ.decompose reql in
  (* matching free point-to predicates *)
  let q_lptos, qf_lptos = List.partition (fun n ->
      let pts = Var.get_eq_closure leqs [n.PoN.hpto_node] in
      Var.diff pts  lqvars0 == []) lptos in
  let q_rptos, qf_rptos = List.partition (fun n ->
      let pts = Var.get_eq_closure (leqs@reqs) [n.PoN.hpto_node] in
      Var.diff pts rqvars0 == []) rptos in
  let l_allocas = Var.get_eq_closure leqs (List.map (fun n -> n.PoN.hpto_node) qf_lptos) in
  let l_nulls = Var.get_eq_closure leqs leqNulls in
  let r_allocas = Var.get_eq_closure reqs (List.map (fun n -> n.PoN.hpto_node) qf_rptos) in
  let r_nulls = Var.get_eq_closure reqs reqNulls in
  (* TODO: consider closure eq *)
  let m_ptos = find_pto_match qf_lptos qf_rptos leqs reqs in
  let fpvns, fpptos = CH.star_decompose e.ENT.fp in
  let fp_allocas = Var.get_eq_closure leqs (List.map (fun n -> n.PoN.hpto_node) fpptos) in
  (* context sensitive-unfolding (or view-pruning) *)
  (* LHS *)
  (* let lunfold_lbls_list = search_ctx_unfold cpreds lvns lp leqNulls leqs lneqs (lptos@fpptos) in *)
  (* if lunfold_lbls_list !=[] then *)
  (*   (\*TODO: unfold all*\) *)
  (*   let lunfold_lbls = List.hd lunfold_lbls_list in *)
  (*   let r= proof_search_unfold cpreds e true lneqs rneqs l_allocas l_nulls r_nulls lunfold_lbls in *)
  (*   [r],[],ENorm *)
  (* else *)
    (* RHS: context sensitive-unfolding (or view-pruning) *)
    let runfold_lbls_list = search_ctx_unfold cpreds rvns rp reqNulls reqs rneqs (rptos@fpptos) in
    if runfold_lbls_list !=[] then
      (*TODO: unfold all*)
      let runfold_lbls = List.hd runfold_lbls_list in
      let r= proof_search_unfold cpreds e false lneqs rneqs l_allocas l_nulls r_nulls runfold_lbls in
      List.map (fun a -> [a]) r,[], ENorm
  else
  match m_ptos with
    | (ln,rn)::_ -> let r, sst = proof_search_match_point_to cpreds e (ln,rn) lqvars0 lbare rqvars0 rbare in
      [r], sst,ENorm
    | [] -> begin
        (* matching preds (not in NF) is sound but incomplete *)
        let m_acpreds, m_cpreds, m_cpreds_end = find_pred_match cpreds lvns lqvars0 leqs l_nulls rvns rqvars0 reqs r_nulls in
        match (m_acpreds@m_cpreds_end) with
          | (ln,rn)::_ -> begin
                (* exclude in the middle *)
                (* let srcs, tars = Cpred.get_src_tar_acyclic cpreds ln.PeN.hpred_name ln.PeN.hpred_arguments in *)
                (* let r = *)
                (*   match (check_excluded srcs tars lneqs) with *)
                (*     | Some (s,r) -> *)
                (*           ps_exclude_middle cpreds (s,r) true ln e *)
                (*     | None -> *)
                          let r = proof_search_match_pred_cond cpreds e (ln,rn) leqs reqs
                in [r],[],ENorm
            end
          | [] -> begin
              try
                (* find a Left pred-pto for unfolding *)
                let lunfold_lbls, _ = search_pred_with_match_alloca cpreds false lvns leqs (r_allocas@r_nulls) in
                let r= proof_search_unfold cpreds e true lneqs rneqs l_allocas l_nulls r_nulls lunfold_lbls in
                [r],[],ENorm
              with Not_found -> begin
                (* find a Right pto-pred for unfolding *)
                try
                  let runfold_lbls, _ = search_pred_with_match_alloca cpreds false rvns reqs (l_allocas@l_nulls) in
                  let rbrs = proof_search_unfold cpreds e false lneqs rneqs l_allocas l_nulls r_nulls runfold_lbls  in
                  if rbrs == [] then [], [], ERuEmp
                  else
                    (* to clone mutiple trees *)
                    let r2 = List.map (fun r -> [r]) rbrs (* proof_search_right_linear_unfold_filter rbrs (lneqs@rneqs) *) in
                    r2,[],ENorm
                with Not_found -> begin
                  (* unfold  base case rhs *)
                  let runfold_lbls = Cpred.search_pred_base_linear_unfold cpreds rvns reqs (l_nulls) in
                  if runfold_lbls != [] then
                    let rbrs =  proof_search_unfold ~ctx_pruning:false cpreds e false lneqs rneqs l_allocas l_nulls r_nulls runfold_lbls in
                    if rbrs == [] then [], [], ERuEmp
                    else
                      (* to clone mutiple trees *)
                      let r = List.map (fun r -> [r]) rbrs (* proof_search_right_linear_unfold_filter rbrs (lneqs@rneqs) *)  in
                      r,[],ENorm
                  else
                    match lvns, rvns with
                    | [],[] ->
                          if lptos == [] || rptos == [] || (qf_lptos == [] && qf_rptos != []) then
                            [],[],ENorm
                          else
                            if qf_lptos != [] && q_rptos!=[] then
                              (* TODO: try all possible: one quantified RHS with all possible qf LHS *)
                              [],[],ENorm
                            else
                              [],[],ENorm
                    | lvn::_, [] -> begin
                        if rptos == [] then
                          (* LUNF - base case*)
                          let lunfold_lbls = search_pred_base_case cpreds lvn in
                          if lunfold_lbls ==[] then [],[],ENorm else
                            let lbrs = proof_search_unfold cpreds e true lneqs rneqs l_allocas l_nulls r_nulls lunfold_lbls in
                            [lbrs],[],ENorm
                        else [],[],ENorm
                      end
                    | [], rvn::_ ->
                        if lptos == [] then
                          (* RUNF - base case*)
                          let runfold_lbls = search_pred_base_case cpreds rvn in
                          if runfold_lbls ==[] then [],[],ENorm else
                            let rbrs = proof_search_unfold cpreds e false lneqs rneqs l_allocas l_nulls r_nulls runfold_lbls in
                            List.map (fun br -> [br]) rbrs, [],ENorm
                        else
                          begin
                            let lallocas_null = (l_allocas@l_nulls) in
                          try
                            let searches1 = proof_search_right_unfold_pred cpreds e
                              (List.length rptos >= List.length lptos) lallocas_null rvns reqs rqvars0 rbare lneqs rneqs l_allocas l_nulls r_nulls in
                            searches1,[],ENorm
                          with Not_found -> begin
                            (* base case unfold *)
                              let vn = List.find (fun vn ->
                                  let src = Cpred.extract_roots cpreds vn in
                                  Var.intersect src lallocas_null == []
                              ) rvns in
                              let runfold_lbls = search_pred_base_case cpreds vn in
                              if runfold_lbls ==[] then [],[],ENorm else
                                let rbrs = proof_search_unfold cpreds e false lneqs rneqs l_allocas l_nulls r_nulls runfold_lbls in
                                List.map (fun br -> [br]) rbrs, [],ENorm
                          end
                      end
                    | _ -> begin try
                        (* match root of rev preds *)
                        let m_rev_preds = find_pred_match_rev cpreds lvns leqs rvns reqs in
                        let m_rev_preds1 = List.filter (fun (ln,_) ->
                            let num_try = Cpred.safe_unfold_num cpreds ln.PeN.hpred_name  in
                            ln.PeN.hpred_unfold_num < num_try) m_rev_preds in
                        match m_rev_preds1 with
                          | (lvn,_)::_ -> begin
                              let r= proof_search_left_unfold_pred cpreds e lvn leqs lneqs rneqs l_allocas l_nulls r_nulls in
                              r
                            end
                          | [] -> raise Not_found
                      with Not_found ->
                          (* match root of diff preds *)
                          let m_preds = find_pred_root_match cpreds true lvns leqs rvns reqs in
                          (* give higher priority for the starting pointers *)
                          let next_ptrs = List.fold_left (fun r pto -> r@pto.PoN.hpto_arguments) [] lptos in
                          let m_preds = List.filter (fun (ln,_) ->
                              let srcs = Cpred.get_root_src_composition cpreds ln.PeN.hpred_name ln.PeN.hpred_arguments in
                              Var.intersect srcs next_ptrs == []
                          ) m_preds in
                          let allocated_svs = (fp_allocas@l_allocas@l_nulls) in
                          match m_preds with
                            | (ln,rn)::_ -> begin
                                let () = Debug.ninfo_hprint (add_str "pred_root_match" (PeN.string_of)) ln no_pos in
                                try
                                  let (lvn,rvn) = try begin
                                    (* ls(x1,x2) |- ls(x1,x3)
                                       only unfold LHS  if x3|->_ or x3=null in either LHS or footprint, src *)
                                    List.find (fun (ln1,rn1) ->
                                        let () = Debug.ninfo_hprint (add_str "ln1" (PeN.string_of)) ln1 no_pos in
                                        let () = Debug.ninfo_hprint (add_str "rn1" (PeN.string_of)) rn1 no_pos in
                                        let _, tars = Cpred.get_root_tar_composition cpreds rn1.PeN.hpred_name rn1.PeN.hpred_arguments in
                                        let () = Debug.ninfo_hprint (add_str "tars" (Var.string_of_list)) tars no_pos in
                                        let () = Debug.ninfo_hprint (add_str "fp_allocas" (Var.string_of_list)) fp_allocas no_pos in
                                        if List.exists (fun sv1 -> List.exists (fun sv2 -> Var.equal sv1 sv2)allocated_svs) tars then true
                                        else
                                          (* let srcs = List.fold_left (fun r vn -> r@(extract_src cpreds vn)) [] lvns in *)
                                          (* Var.intersect tars srcs != [] *)
                                          false
                                    ) m_preds
                                  end
                                  with Not_found ->
                                      List.find (fun (ln,rn) ->
                                          let num_try = Cpred.safe_unfold_num cpreds ln.PeN.hpred_name  in
                                          (ln.PeN.hpred_unfold_num < num_try) ||
                                              (Var.intersect (Cpred.extract_roots cpreds ln)
                                                  (Cpred.extract_roots cpreds rn) != [] && not (is_match_pred cpreds e))
                                      ) m_preds in
                                  let r= proof_search_left_unfold_pred cpreds e lvn leqs lneqs rneqs l_allocas l_nulls r_nulls in
                                  r
                                with Not_found ->
                                    (* below is for soundness but not completeness*)
                                    let try_search1 =
                                      (* unfold pred with matched roots in both sides *)
                                      (* if (List.length lptos) != (List.length rptos) then *)
                                      proof_search_try_unfold_pred_pred cpreds e (ln, rn)
                                          lbare lptos lqvars0
                                          rbare rptos rqvars0 lneqs rneqs l_allocas l_nulls r_nulls
                                    in
                                    (* else *)
                                    let try_search2 =
                                      (* condition match *)
                                      if (List.length lptos) == (List.length rptos) &&
                                        List.length lvns == List.length rvns &&
                                        List.for_all (fun lvn ->
                                            List.exists (fun rvn ->
                                                Ustr.str_eq lvn.PeN.hpred_name rvn.PeN.hpred_name) rvns) lvns
                                      then
                                        List.fold_left (fun r (ln,rn) ->
                                            if Ustr.str_eq ln.PeN.hpred_name rn.PeN.hpred_name then
                                              let r1 = proof_search_try_match_pred_pred cpreds e (ln, rn)
                                                leqs reqs
                                              in r@[r1]
                                            else r
                                        ) [] m_preds
                                      else []
                                    in
                                    let try_search = try_search1@try_search2 in
                                    let searches0, es = if try_search ==[] then
                                      try
                                        let lvn = List.find (fun lvn -> List.for_all (fun rvn ->
                                            lvn.PeN.hpred_unfold_num < rvn.PeN.hpred_unfold_num
                                        ) rvns) lvns in
                                        let r, _, es= proof_search_left_unfold_pred cpreds e lvn leqs lneqs rneqs l_allocas l_nulls r_nulls in
                                        r,es
                                      with Not_found -> [], ENorm
                                    else try_search, ENorm
                                    in
                                    (* first empty to avoid incomplete conclusion *)
                                    [[]]@searches0, [],es
                              end
                            | [] -> begin
                                try
                                  (*a LHS predicate whose unfolding number is < all unfolding number of RHS*)
                                  let lvn = List.find (fun lvn -> List.for_all (fun rvn ->
                                      lvn.PeN.hpred_unfold_num < rvn.PeN.hpred_unfold_num
                                  ) rvns) lvns in
                                  let r,sst,es= proof_search_left_unfold_pred cpreds e lvn leqs lneqs rneqs l_allocas l_nulls r_nulls in
                                  if es==ELuEmp then (r,sst,es) else
                                  [[]]@r, [],ENorm
                                with Not_found -> begin
                                  try
                                    (* find a Left pred-pto for unfolding based on bases *)
                                    let lunfold_lbls, _ = search_pred_with_match_alloca cpreds true lvns leqs (r_allocas@r_nulls) in
                                    let r= proof_search_unfold cpreds e true lneqs rneqs l_allocas l_nulls r_nulls lunfold_lbls in
                                    let search =  [[]]@[r] in
                                    search,[],ENorm
                                  with Not_found ->  begin
                                    (* find a Right pto-pred for unfolding based on bases *)
                                    try
                                      let runfold_lbls, _ = search_pred_with_match_alloca cpreds true rvns reqs (l_allocas@l_nulls) in
                                      let rbrs =  proof_search_unfold cpreds e false lneqs rneqs l_allocas l_nulls r_nulls runfold_lbls in
                                      (* to clone mutiple trees *)
                                      let searches0 = (List.map (fun br -> [br]) rbrs) in
                                      let searches1 = if lvns == [] then  searches0 else [[]]@searches0 in
                                      searches1,[],ENorm
                                    with Not_found ->  begin
                                      try
                                        let searches0 =  proof_search_right_unfold_pto_pred cpreds e rvns reqs (l_allocas@l_nulls) rqvars0 rbare lneqs rneqs l_allocas l_nulls r_nulls in
                                        [[]]@searches0,[],ENorm
                                      with Not_found -> [],[],ENorm
                                    end
                                  end
                                end
                              end
                      end
                end
              end
            end
      end

let proof_search cpreds is_ho e=
  let pr1 = ENT.string_of in
  let pr2 = pr_list_ln (pr_pair pr1 string_of) in
  let pr_out = pr_triple (pr_list_ln pr2) (pr_list Var.string_of_pair) Com.string_of_entstuck in
  Debug.no_1 "proof_search" pr1 pr_out
      (fun _ -> proof_search_x cpreds is_ho  e) e
