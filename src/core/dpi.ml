open Globals
open Ustr
open VarGen
open Gen.Basic

module CF = Cformula
module CB = Csymheap
module CH = Cheap
module CPeN = CpredNode
module CPoN = CptoNode
module CP = Cpure
module T = Term
module DD = Debug

let num_PROJ = "n__"
let idx_VAR = "idx"

let is_dpi_rel p0=
  let rec is_dpi_e e= match e with
    | Exp.Null _ | Exp.Var _ | Exp.IConst _ -> true
    | Exp.Add (e1, e2, _ ) | Exp.Subtract (e1, e2, _ ) -> begin
        if (is_dpi_e e1) && (is_dpi_e e2) then
          let svs1 = Exp.fv e1 in
          let svs2 = Exp.fv e2 in
          List.length (svs1@svs2) < 2
        else false
          end
    | Exp.Min (e1, e2, _ ) | Exp.Max (e1, e2, _ )
          -> (is_dpi_e e1) && (is_dpi_e e2)
    | _ -> false
  in
  let rec  aux_check p=
    match p with
      | CP.BForm t -> begin
          match t with
            | T.BConst _ | T.BVar _ -> true
            | T.Lt (e1,e2,_) | T.Lte (e1,e2,_)
            | T.Gt (e1,e2,_) | T.Gte (e1,e2,_)
            | T.Eq (e1,e2,_) | T.Neq (e1,e2,_) -> (is_dpi_e e1) && (is_dpi_e e2)
            | _ -> false
        end
      | CP.Exists (_, p1) -> aux_check p1
      | CP.Forall (_, p1) -> aux_check p1
      | CP.Not p1 -> aux_check p1
      | _ -> false
  in
  let ps = CP.split_conjunctions p0 in
  List.for_all aux_check ps

let is_dpi_self_rec_x rel_id args f is_linear_compos=
  let term_detect_rec t=
    match t with
      | T.RelForm (id, exps, pos) ->
            if Ustr.str_eq rel_id id (* id.Var.id*) then
              (Exp.afv_list exps)
            else []
      | _ -> []
  in
  let detect_rec_rel p=
    match p with
      | CP.BForm t -> term_detect_rec t
      | _ -> []
  in
  let rec proj_base args heap_ps ps r=
    match args with
      | a::rest -> if ps == [] then (true, r) else
            if Var.is_node a then
              proj_base rest heap_ps ps r
            else
              let in_ps, rem = List.partition (fun p ->
                  let svs = (CP.fv p) in
                  List.for_all (fun v ->
                      Var.equal v a
                  ) svs
              ) ps in
              if in_ps == [] then
                proj_base rest heap_ps ps r
              else
                let new_part = CP.join_conjunctions (in_ps@heap_ps)no_pos in
                proj_base rest heap_ps rem (r@[([a], new_part)])
      | [] -> if ps==[] then
          (true, r)
        else
          (false, r)
  in
  let rec proj_linear_base args heap_ps ps r=
    match ps with
      | p::rest -> if args == [] then (true, r) else
          let svs = (CP.fv p) in
          let non_heap_svs = List.filter (fun v -> not (Var.is_node v)) svs in
            if non_heap_svs == [] then
              proj_linear_base args heap_ps rest r
            else
              let rest_args = Var.diff args non_heap_svs in
              let new_part = CP.join_conjunctions ([p]@heap_ps) no_pos in
              proj_linear_base rest_args heap_ps rest (r@[(non_heap_svs, new_part)])
      | [] -> (true, r)
  in
  let split_head args_list = List.fold_left (fun (r1,r2) ls ->
              match ls with
                | x::tl -> (r1@[x], r2@[tl])
                | [] -> raise Not_found
          ) ([],[]) args_list
  in
  let rec proj_rec args rec_args_ls heap_ps ps r=
    match args with
      | a::rest -> begin try
          if ps == [] then (true, r) else
          let rec_args, rest_rec_args_ls = split_head rec_args_ls in
          let () = Debug.ninfo_hprint (add_str ("rec_args") (Var.string_of_list)) rec_args no_pos in
          if Var.is_node a then
             proj_rec rest rest_rec_args_ls heap_ps ps r
          else
            let grp_args = rec_args@[a] in
            let () = Debug.ninfo_hprint (add_str ("grp_args") (Var.string_of_list)) grp_args no_pos in
            let in_ps, rem = List.partition (fun p ->
                let svs = (CP.fv p) in
                List.for_all (fun v1 -> begin
                  List.exists (fun  v2 -> Var.equal v1 v2) grp_args
                end
                ) svs
            ) ps in
            if in_ps == [] then
              proj_rec rest rest_rec_args_ls heap_ps ps r
            else
              let new_part = CP.join_conjunctions (in_ps@heap_ps)no_pos in
              let () = Debug.ninfo_hprint (add_str ("new_part") (CP.string_of)) new_part no_pos in
              proj_rec rest rest_rec_args_ls heap_ps rem (r@[([a], new_part)])
        with _ -> false, r
        end
      | [] -> if ps==[] then
          (true, r)
        else
          (false, r)
  in
  let rec fleft fs r =
    match fs with
      | f::rest -> begin
          let qvars, bare = CP.split_quantifiers f in
          let () = Debug.ninfo_hprint (add_str ("bare") (CP.string_of)) bare no_pos in
          let ps = CP.split_conjunctions bare in
          let rec_args_ls = List.fold_left (fun r1 p ->
              let rec_args = detect_rec_rel p in
              if rec_args = [] then
                r1
              else
                r1@[rec_args]
          ) [] ps in
          let () = Debug.ninfo_hprint (add_str ("rec_args_ls") (pr_list_ln (Var.string_of_list ))) rec_args_ls no_pos in
          let heap_ps, rem = List.partition (fun p ->
              let svs = (CP.fv p) in
              (List.for_all Var.is_node svs) ||
                  (List.for_all (fun v -> Var.mem v qvars) svs ) ||
                   (detect_rec_rel p) != []
          ) ps in
          let () = Debug.ninfo_hprint (add_str ("heap_ps") (pr_list CP.string_of)) heap_ps no_pos in
          let () = Debug.ninfo_hprint (add_str ("rem") (pr_list CP.string_of)) rem no_pos in
          if List.length rec_args_ls == 0 then
            (* base case*)
            if is_linear_compos then
              let is_deci,base_ps = proj_linear_base args heap_ps rem [] in
              if is_deci then
                fleft rest (r@base_ps)
              else false, r
            else
              let is_deci,base_ps = proj_base args heap_ps rem [] in
              if is_deci then
                fleft rest (r@base_ps)
              else false, r
          else
            (* rec_case *)
            let is_deci, rec_ps = proj_rec args rec_args_ls heap_ps rem []  in
            if is_deci then
              fleft rest (r@rec_ps)
            else false, r
        end
      | [] -> true, r
  in
  let rec group ls res=
    match ls with
      | (svs, f)::rest ->
            let same_grp, rem = List.partition (fun (svs2, f2) -> Var.intersect svs svs2 != []) rest in
            let n_grp = List.fold_left (fun (ls, f) (ls1, f1) ->
                (ls@ls1, CP.mkOr f f1 no_pos)
            ) (svs, f) same_grp in
            group rem res@[n_grp ]
      | [] -> res
  in
  let fs = CP.split_disjunctions f in
  let is_deci, parts = fleft fs [] in
  let () = Debug.ninfo_hprint (add_str ("parts") (pr_list_ln (pr_pair Var.string_of_list CP.string_of))) parts no_pos in
  if is_deci then
    let grps = group parts [] in
    is_deci, List.map snd grps
  else
    is_deci, [f]

let is_dpi_self_rec relid args f is_linear_compos=
  let pr1 = Var.string_of_list in
  let pr2 = CP.string_of in
  let pr_out = pr_pair string_of_bool (pr_list CP.string_of) in
  Debug.no_3 "is_dpi_self_rec" pr_id pr1 pr2 pr_out
      (fun _ _ _ -> is_dpi_self_rec_x relid args f is_linear_compos)
      relid args f

let pure_projection_heap lower_invs h0=
  let rec helper h= match h with
    | CH.Star (h1, h2, pos) ->
          CP.mkAnd (helper h1) (helper h2) pos
    | CH.PtoNode {CPoN.hpto_node = sv; CPoN.hpto_pos = pos} ->
          CP.mkGtZeroExp (Exp.mkVar sv pos) pos
    | CH.PredNode {CPeN.hpred_name = c; CPeN.hpred_arguments = svs;
      CPeN.hpred_pos = pos;
      } -> begin try
        let (_, (fargs, inv)) = List.find (fun (id, _) -> Ustr.str_eq id c) lower_invs in
        let sst = List.combine fargs svs in
        CP.subst_var sst inv
      with _ ->
          (* let relid = Var.mk_unprimed (RelT (List.map Var.type_of svs)) (num_PROJ^c) in *)
          let relid = num_PROJ^c in
          let relT = Term.RelForm (relid, (List.map (fun sv -> Exp.mkVar sv pos) svs), pos) in
          CP.BForm relT
      end
    | CH.HTrue | CH.HEmp -> CP.mkEqZeroExp (Exp.mkIConst 0 no_pos) no_pos
    | CH.HFalse -> CP.mkEqZeroExp (Exp.mkIConst 1 no_pos) no_pos
  in helper h0

let pure_projection_formula lower_invs f0=
  let pure_projection_base fb=
    CP.mkAnd (pure_projection_heap lower_invs fb.CB.base_heap)
        fb.CB.base_pure fb.CB.base_pos
  in
  let rec helper f=
    match f with
      | CF.Or (f1, f2, pos) ->
            CP.mkOr (helper f1) (helper f2) pos
      | CF.Base fb ->
            pure_projection_base fb
      | CF.Exists (fb, svs) ->
            CP.mkExists svs (pure_projection_base fb) fb.CB.base_pos
  in helper f0

let insert_idx_constr rel_id n_rel_header idx_sv p0=
  let term_detect_rec t=
    match t with
      | T.RelForm (id, exps, pos) ->
            if Ustr.str_eq rel_id id (* id.Var.id *) then
              let n_idx = Var.fresh_var idx_sv in
              [n_idx], T.RelForm (n_rel_header, exps@[Exp.mkVar n_idx no_pos], pos)
            else [], t
      | _ -> [],t
  in
  let rec helper p= match p with
    | CP.BForm t -> let rec_args, n_t =  term_detect_rec t in
      rec_args, CP.BForm n_t
    | CP.Not p1 -> let rec_args, n_p1 = helper p1 in
      rec_args, CP.Not n_p1
    | CP.Exists (sv, p1) -> let rec_args, n_p1 = helper p1 in
         rec_args, CP.Exists (sv, n_p1)
    | CP.Forall (sv, p1) -> let rec_args, n_p1 = helper p1 in
      rec_args, CP.Forall (sv, n_p1)
    | CP.And (f1, f2) -> let rec_args1, n_f1 = helper f1 in
      let rec_args2, n_f2 = helper f2 in
      rec_args1@rec_args2, CP.And (n_f1, n_f2)
    | CP.Or (f1, f2) -> Gen.report_error no_pos "DPI: can not happen"
  in
  let base_idx = CP.mkEqZeroExp (Exp.mkVar idx_sv no_pos) no_pos in
  let ps = CP.split_disjunctions p0 in
  let n_ps = List.map (fun p ->
      let rec_args, np = helper p in
      let period_constr = match rec_args with
        | [] -> base_idx
        | sv::_ -> CP.mkEqExp (Exp.mkVar idx_sv no_pos)
              (Exp.Add (Exp.mkVar sv no_pos, (Exp.mkIConst 1 no_pos), no_pos))
                  no_pos
          in
          CP.mkAnd np period_constr no_pos
  ) ps in
  CP.join_disjunctions n_ps

let insert_idx rel_id args p=
  let idx_sv = Var.mk_unprimed Int (fresh_any_name idx_VAR) in
  let n_rel_header = (* Var.mk_unprimed (RelT ((List.map Var.type_of args)@[Int])) *) rel_id in
  let n_args = args@[idx_sv] in
  let n_p = insert_idx_constr rel_id n_rel_header idx_sv p in
  (rel_id, n_args, n_p)

let is_single_self_rec pred_name f0=
  let rec aux fs=
    match fs with
      | f::rest -> begin
            let vns, _ = CF.star_decompose f in
            match vns with
              | [] -> aux rest
              | [vn] -> if  Ustr.str_eq vn.CpredNode.hpred_name pred_name then
                  (* is arith *)
                  let _, _, _, p = CF.decompose f in
                  if is_dpi_rel p then
                    aux rest
                  else false
                else false
              | _ -> false
        end
      | [] -> true
  in
  let fs = CF.list_of_disjuncts f0 in
  aux fs

let to_pure_self_rec_x pred_name args is_linear_compos lower_invs f=
  let rel_id = num_PROJ ^ pred_name in
  let rel_defn = pure_projection_formula lower_invs f in
  if is_linear_compos && List.exists (fun v -> not (Var.is_node v)) args then
    let is_deci, defs = is_dpi_self_rec rel_id args rel_defn is_linear_compos in
    (is_deci, List.map (fun f ->
        insert_idx rel_id args f
        (* (rel_id, args, f) *)
    ) defs)
  else
    (* insert idx parameter *)
    let is_deci1 = List.for_all Var.is_node args in
    let is_single_rec = is_single_self_rec pred_name f in
    let a, b, c = insert_idx rel_id args rel_defn in
    (is_linear_compos || is_deci1 || is_single_rec , [(a, b, c)])

let to_pure_self_rec pred_name args is_linear_compos lower_invs f=
  let pr1 = pr_list Var.string_of in
  let pr2 = pr_triple pr_id pr1  CP.string_of in
  let pr_out = pr_pair string_of_bool (pr_list_ln pr2) in
  let pr3 = CF.string_of in
  Debug.no_4 "to_pure_self_rec" pr_id pr1 string_of_bool pr3 pr_out
      (fun _ _ _ _ -> to_pure_self_rec_x pred_name args is_linear_compos lower_invs f)
      pred_name args is_linear_compos f
