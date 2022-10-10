open Globals
open Gen
open VarGen

open Cpure
open Term

open Com

module ENTRY = StrNode.STR_NODE_DATA
module N = StrNode.STRNODE
module E = StrEdge.STREDGE
module CP = Cpure



(*************************************************************)
(*************************************************************)
(*                       PARIKH                              *)
(*************************************************************)
(*************************************************************)
let aux_cfg2parikh_first_component sv prod_vars=
  let sum1, sum2 = List.fold_left (fun (p1,p2)
    (yp, lhs_sv, (rhs_distinct_vars, count_rhs_vars),
    (rhs_distinct_letters, count_rhs_letters ) ) -> begin
        let n_p1 = try
          let _, n =  List.find (fun (sv1, _) ->
              Var.equal sv sv1) count_rhs_vars in
          let matric = if n = 1 then yp else
            Exp.Mult (Exp.IConst (n, no_pos), yp, no_pos) in
          Exp.Add (p1, matric, no_pos)
        with Not_found -> p1
        in
        let n_p2 = if Var.equal sv lhs_sv then
          Exp.Add (*Subtract*) (p2, yp, no_pos)
        else p2
        in
        (n_p1, n_p2)
    end
  ) (Exp.mkZero no_pos, Exp.mkZero no_pos) prod_vars in
  Exp.Subtract (sum1, sum2, no_pos)

let aux_cfg2parikh_second_component x_z_letters prod_vars c=
  let sum = List.fold_left (fun (p1)
    (yp, lhs_sv, (rhs_distinct_vars, count_rhs_vars),
    (rhs_distinct_letters, count_rhs_letters ) ) -> begin
        let n_p1 = try
          let _, n =  List.find (fun (c1, _) ->
              Exp.eqExp_f Var.equal c c1) count_rhs_letters in
          let matric = if n = 1 then yp else
            Exp.Mult (Exp.IConst (n, no_pos), yp, no_pos) in
          Exp.Add (p1, matric, no_pos)
        with Not_found -> p1
        in
        n_p1
    end
  ) (Exp.mkZero no_pos) prod_vars in
  let _, xc, zc = List.find (fun (c1,_,_) -> Exp.eqExp_f Var.equal c c1
  ) x_z_letters in
  let f2_1 = CP.BForm (Term.mkEq xc sum no_pos) in
  let f2_21 = CP.BForm (Term.mkEqZero xc no_pos) in
  let f2_22 = CP.BForm (Term.mkGtZero zc no_pos) in
  CP.mkAnd f2_1 (CP.mkOr f2_21 f2_22 no_pos) no_pos

let aux_cfg2parikh_3nd_component_letter sv0 x_z_letters z_vars prod_vars c=
  let (_, _, zc) = List.find (fun (c1, _, _) ->
      Exp.eqExp_f Var.equal c c1
  ) x_z_letters in
  let disj = List.fold_left (fun (p1)
    (yp, lhs_sv, (rhs_distinct_vars, count_rhs_vars),
    (rhs_distinct_letters, count_rhs_letters ) ) -> begin
      if List.exists (fun (c1, _) ->
          Exp.eqExp_f Var.equal c c1) count_rhs_letters then
        let np2 = CP.BForm (Term.mkGtZero yp no_pos) in
        (* if lhs_sv is sv0 *)
        let np = if Var.equal lhs_sv sv0 then
          let np1 = CP.BForm (Term.mkEqN zc 1 no_pos) in
          CP.mkAnd np1 np2 no_pos
        else
          let (_, zX) = List.find (fun (sv, _) ->
              Var.equal sv lhs_sv
          ) z_vars in
          let rhs_1 = Exp.Add (zX, Exp.mkN 1 no_pos, no_pos) in
          let np3 = CP.mkEqExp zc rhs_1 no_pos in
          let np4 = CP.BForm (Term.mkGtZero zX no_pos) in
          CP.mkAnd (CP.mkAnd np3 np2 no_pos) np4 no_pos
        in
        CP.mkOr p1 np no_pos
      else p1
    end
  ) (CP.mkEqZeroExp zc no_pos) prod_vars in
  disj

let aux_cfg2parikh_3nd_component_var sv0 z_vars prod_vars sv=
  let ( _, zs) = List.find (fun (sv1, _) ->
      Var.equal sv sv1
  ) z_vars in
  let disj = List.fold_left (fun (p1)
    (yp, lhs_sv, (rhs_distinct_vars, count_rhs_vars),
    (rhs_distinct_letters, count_rhs_letters ) ) -> begin
      if List.exists (fun (sv1, _) ->
          Var.equal sv sv1) count_rhs_vars then
        let np2 = CP.BForm (Term.mkGtZero yp no_pos) in
        (* if lhs_sv is sv0 *)
        let np = if Var.equal lhs_sv sv0 then
          let np1 = CP.BForm (Term.mkEqN zs 1 no_pos) in
          CP.mkAnd np1 np2 no_pos
        else
          let (_, zX) = List.find (fun (sv, _) ->
              Var.equal sv lhs_sv
          ) z_vars in
          let rhs_1 = Exp.Add (zX, Exp.mkN 1 no_pos, no_pos) in
          let np3 = CP.mkEqExp zs rhs_1 no_pos in
          let np4 = CP.BForm (Term.mkGtZero zX no_pos) in
          CP.mkAnd (CP.mkAnd np3 np2 no_pos) np4 no_pos
        in
        CP.mkOr p1 np no_pos
      else p1
    end
  ) (CP.mkEqZeroExp zs no_pos) prod_vars in
  disj

let cfg2parikh_aux_vars alphabet vars prods (* vars_in_arith *)=
  let rec update_var_prod lhs_sv yp cur res =
    match cur with
      | [] -> res
      | (sv, sls)::rest ->
            if Var.equal sv lhs_sv then
              res@[(sv, sls@[yp])]@rest
            else update_var_prod lhs_sv yp rest (res@[(sv, sls)])
  in
  (* new int vars *)
  let x_z_letters = List.map (fun c ->
      let xc = Var.mk_unprimed Int (fresh_old_name "x") in
      let zc = Var.mk_unprimed Int (fresh_old_name "z") in
      (c, Exp.mkVar xc no_pos, Exp.mkVar zc no_pos)) alphabet in
  let z_vars = List.map (fun v ->
      let zv = Var.mk_unprimed Int (fresh_old_name "z") in
      (v, Exp.mkVar zv no_pos)) vars in
  (* vars for production *)
  (*
    |lhs_sv| = \sigma (prod_vars)
  *)
  (* let map_var_prod = List.map (fun sv -> (sv, []))  vars_in_arith in *)
  let prod_vars(* ,map_var_prod *) = List.fold_left (fun (r1(* ,r2 *)) (lhs_sv, e)  ->
      let rhs_vars = Exp.fv ~dups:true e in
      let rhs_distinct_vars = (Var.remove_dups rhs_vars) in
      let count_rhs_vars = List.map (fun sv ->
          let all_sv = List.filter (Var.equal sv) rhs_vars in
          (sv, List.length all_sv)
      ) rhs_distinct_vars in

      let () = Debug.ninfo_hprint(add_str "\nRHS:\n" (Exp.string_of)) e no_pos in
      let rhs_letters = Exp.get_cconst e in
      let () = Debug.ninfo_hprint(add_str "\nrhs_letters:\n" (pr_list Exp.string_of)) rhs_letters no_pos in
      let rhs_distinct_letters = BList.remove_dups_eq (Exp.eqExp_f Var.equal) rhs_letters in
      let count_rhs_letters = List.map (fun c ->
          let all_c = List.filter (Exp.eqExp_f Var.equal c) rhs_letters in
          (c, List.length all_c)
      ) rhs_distinct_letters in
      let yp = Var.mk_unprimed Int (fresh_old_name "p") in
      let acc_r1 = r1@[(Exp.mkVar yp no_pos, lhs_sv, (rhs_distinct_vars, count_rhs_vars),
      (rhs_distinct_letters, count_rhs_letters ) )] in
      (* let acc_r2 = if Exp.isEmpCConst e then r2 else *)
      (*   update_var_prod lhs_sv yp r2 [] in *)
      (acc_r1(* , acc_r2 *))
  )  ([](* , map_var_prod *) ) prods in
  (* let map_var_prods = List.map (fun (sv, ps) -> *)
  (*     if ps == [] then *)
  (*       (sv, Cpure.mkTrue no_pos) *)
  (*     else *)
  (*       let rhs = List.fold_left (fun r sv-> *)
  (*           Exp.Add (r, Exp.mkVar sv no_pos, no_pos) *)
  (*       ) (Exp.mkVar (List.hd ps) no_pos) *)
  (*         (List.tl ps) in *)
  (*       let isv = Var.lookup_length_var_of_string sv in *)
  (*       (sv, Cpure.mkEqExp (Exp.mkVar isv no_pos) rhs no_pos) *)
  (* ) map_var_prod in *)
  let pr0a = (pr_list (pr_pair Exp.string_of string_of_int)) in
  let pr0b = (pr_list (pr_pair Var.string_of string_of_int)) in
  let pr1 = pr_pair (pr_list Exp.string_of) pr0a in
  let pr_prod = pr_quad (Exp.string_of) (Var.string_of) (pr_pair (Var.string_of_list) pr0b) pr1 in
   let () = Debug.ninfo_hprint(add_str "\nprod_vars:\n" (pr_list pr_prod)) prod_vars no_pos in
   (x_z_letters, z_vars, prod_vars(* , map_var_prods *))



let cfg2parik_2nd_component alphabet vars prods (x_z_letters, z_vars, prod_vars)=
  (* 2nd component *)
  let c_head = List.hd alphabet in
  let f2_head = aux_cfg2parikh_second_component x_z_letters prod_vars c_head in
  let () = Debug.ninfo_hprint(add_str "\nf2_head:\n" (CP.string_of)) f2_head no_pos in
  let f2 = List.fold_left (fun acc_f2 c->
      let f2_c =  aux_cfg2parikh_second_component x_z_letters prod_vars c in
      CP.mkAnd acc_f2 f2_c no_pos
  ) f2_head (List.tl alphabet) in
   let () = Debug.ninfo_hprint(add_str "\nsecond component:\n" (CP.string_of)) f2 no_pos in
   f2

(* no long is used*)
let cfg2parikh_old alphabet vars prods (x_z_letters, z_vars, prod_vars) sv=
  let rec get_rest ls sv res=
    match ls with
      | [] -> res
      | sv1::rest -> if Var.equal sv sv1 then res@rest
        else get_rest rest sv (res@[sv1])
  in
  let not_start_vars = get_rest vars sv [] in
  (* new int vars *)
  let x_z_letters = List.map (fun c ->
      let xc = Var.mk_unprimed Int (fresh_old_name "x") in
      let zc = Var.mk_unprimed Int (fresh_old_name "z") in
      (c, Exp.mkVar xc no_pos, Exp.mkVar zc no_pos)) alphabet in
  let z_vars = List.map (fun v ->
      let zv = Var.mk_unprimed Int (fresh_old_name "z") in
      (v, Exp.mkVar zv no_pos)) vars in
  (* vars for production *)
  let prod_vars = List.map (fun (lhs_sv, e) ->
      let rhs_vars = Exp.fv ~dups:true e in
      let rhs_distinct_vars = (Var.remove_dups rhs_vars) in
      let count_rhs_vars = List.map (fun sv ->
          let all_sv = List.filter (Var.equal sv) rhs_vars in
          (sv, List.length all_sv)
      ) rhs_distinct_vars in

      let () = Debug.ninfo_hprint(add_str "\nRHS:\n" (Exp.string_of)) e no_pos in
      let rhs_letters = Exp.get_cconst e in
      let () = Debug.ninfo_hprint(add_str "\nrhs_letters:\n" (pr_list Exp.string_of)) rhs_letters no_pos in
      let rhs_distinct_letters = BList.remove_dups_eq (Exp.eqExp_f Var.equal) rhs_letters in
      let count_rhs_letters = List.map (fun c ->
          let all_c = List.filter (Exp.eqExp_f Var.equal c) rhs_letters in
          (c, List.length all_c)
      ) rhs_distinct_letters in
      let yp = Var.mk_unprimed Int (fresh_old_name "y") in
      (Exp.mkVar yp no_pos, lhs_sv, (rhs_distinct_vars, count_rhs_vars),
      (rhs_distinct_letters, count_rhs_letters ) )
  ) prods in
  let pr0a = (pr_list (pr_pair Exp.string_of string_of_int)) in
  let pr0b = (pr_list (pr_pair Var.string_of string_of_int)) in
  let pr1 = pr_pair (pr_list Exp.string_of) pr0a in
  let pr_prod = pr_quad (Exp.string_of) (Var.string_of) (pr_pair (Var.string_of_list) pr0b) pr1 in
   let () = Debug.ninfo_hprint(add_str "\nprod_vars:\n" (pr_list pr_prod)) prod_vars no_pos in
  (* 1st component *)
  let e1_start = aux_cfg2parikh_first_component sv prod_vars in
  let e1_start1 = Exp.Add (Exp.IConst (1, no_pos), e1_start, no_pos) in
  let f1_start = CP.BForm (Term.mkEqZero e1_start1 no_pos) in
  let f1 = List.fold_left (fun acc_f sv1 ->
       let e1 = aux_cfg2parikh_first_component sv1 prod_vars in
       let f1 = CP.BForm (Term.mkEqZero e1 no_pos) in
       CP.mkAnd acc_f f1 no_pos
  ) f1_start not_start_vars in
  let () = Debug.ninfo_hprint(add_str "\nfirst component:\n" (CP.string_of)) f1 no_pos in
  (* 2nd component *)
  let c_head = List.hd alphabet in
  let f2_head = aux_cfg2parikh_second_component x_z_letters prod_vars c_head in
  let () = Debug.ninfo_hprint(add_str "\nf2_head:\n" (CP.string_of)) f2_head no_pos in
  let f2 = List.fold_left (fun acc_f2 c->
      let f2_c =  aux_cfg2parikh_second_component x_z_letters prod_vars c in
      CP.mkAnd acc_f2 f2_c no_pos
  ) f2_head (List.tl alphabet) in
   let () = Debug.ninfo_hprint(add_str "\nsecond component:\n" (CP.string_of)) f2 no_pos in

  (* 3rd component *)
   let f3_var_head = aux_cfg2parikh_3nd_component_var sv z_vars prod_vars sv in
   let f3_var = List.fold_left (fun acc_f3_var sv1 ->
       let f3_var = aux_cfg2parikh_3nd_component_var sv z_vars prod_vars sv1 in
       CP.mkAnd acc_f3_var f3_var no_pos
   ) f3_var_head not_start_vars in
   let f3 =  List.fold_left (fun acc_f3_letter c1 ->
       let f3_letter = aux_cfg2parikh_3nd_component_letter sv x_z_letters z_vars
         prod_vars c1 in
       CP.mkAnd acc_f3_letter f3_letter no_pos
   ) f3_var alphabet in
   let () = Debug.ninfo_hprint(add_str "\nthird component:\n" (CP.string_of)) f3 no_pos in

   (* let inv_letter_count = List.fold_left (fun r (_, xc, _) -> *)
   (*     let inv_c = CP.mkGteZeroExp xc no_pos in *)
   (*     CP.mkAnd r inv_c no_pos *)
   (* ) (CP.mkTrue no_pos) x_z_letters  in *)
  let comb  = CP.mkAnd (CP.mkAnd f1 (* (CP.mkAnd f1 inv_letter_count no_pos) *) f2 no_pos)
    f3 no_pos in
  (* |x| = n_a + n_b *)
  let isv = Var.lookup_length_var_of_string sv in
  let length = if x_z_letters = [] then CP.mkTrue no_pos else
    CP.mkEqExp (Exp.mkVar isv no_pos) (Exp.mkAdd_list (List.map (fun (_, xc, _) -> xc ) x_z_letters) no_pos) no_pos
  in
  let comb_length = CP.mkAnd length comb no_pos in
  let quans = (List.map (fun (y, _, _,_) -> y) prod_vars)@
    (List.map (fun (_,zx) -> zx) z_vars)@
    (List.map (fun (_, _, zc) -> zc ) x_z_letters)in
  let r_count = CP.add_quantifiers
    (List.fold_left (fun r e -> r@(Exp.fv e)) [] quans) comb_length in
  r_count

let cfg2parikh_x alphabet vars prods (x_z_letters, z_vars, prod_vars) f2 (* rel_f *) sv=
  let rec get_rest ls sv res=
    match ls with
      | [] -> res
      | sv1::rest -> if Var.equal sv sv1 then res@rest
        else get_rest rest sv (res@[sv1])
  in
  let not_start_vars = get_rest vars sv [] in

  (* 1st component *)
  let e1_start = aux_cfg2parikh_first_component sv prod_vars in
  let e1_start1 = Exp.Add (Exp.IConst (1, no_pos), e1_start, no_pos) in
  let f1_start = CP.BForm (Term.mkEqZero e1_start1 no_pos) in
  let f1 = List.fold_left (fun acc_f sv1 ->
       let e1 = aux_cfg2parikh_first_component sv1 prod_vars in
       let f1 = CP.BForm (Term.mkEqZero e1 no_pos) in
       CP.mkAnd acc_f f1 no_pos
  ) f1_start not_start_vars in
  let () = Debug.ninfo_hprint(add_str "first component:\n" (CP.string_of)) f1 no_pos in
  let f1 = simplify_fnc f1 in
  let () = Debug.ninfo_hprint(add_str "first component (simplified):\n" (CP.string_of)) f1 no_pos in
  (* 2nd component *)
  (* f2 *)

  (* 3rd component *)
   let f3_var_head = aux_cfg2parikh_3nd_component_var sv z_vars prod_vars sv in
   let f3_var = List.fold_left (fun acc_f3_var sv1 ->
       let f3_var = aux_cfg2parikh_3nd_component_var sv z_vars prod_vars sv1 in
       CP.mkAnd acc_f3_var f3_var no_pos
   ) f3_var_head not_start_vars in
   let f3 =  List.fold_left (fun acc_f3_letter c1 ->
       let f3_letter = aux_cfg2parikh_3nd_component_letter sv x_z_letters z_vars
         prod_vars c1 in
       CP.mkAnd acc_f3_letter f3_letter no_pos
   ) f3_var alphabet in
   let () = Debug.ninfo_hprint(add_str "\nthird component:\n" (CP.string_of)) f3 no_pos in

   (* let inv_letter_count = List.fold_left (fun r (_, xc, _) -> *)
   (*     let inv_c = CP.mkGteZeroExp xc no_pos in *)
   (*     CP.mkAnd r inv_c no_pos *)
   (* ) (CP.mkTrue no_pos) x_z_letters  in *)
   let comb  = CP.mkAnd (CP.mkAnd f1 (* (CP.mkAnd f1 inv_letter_count no_pos) *) f2 no_pos)
    f3 no_pos in
  (* |x| = n_a + n_b *)
  let isv = Var.lookup_length_var_of_string sv in
  let length = if x_z_letters = [] then CP.mkTrue no_pos else
    let letter_counts = (List.map (fun (_, xc, _) -> xc ) x_z_letters) in
    let bare = CP.mkEqExp (Exp.mkVar isv no_pos) (Exp.mkAdd_list letter_counts no_pos) no_pos in
    bare
  in
   (* let inv_isv = CP.mkGteZeroExp isv no_pos in *)
  let comb_length = CP.mkAnd length comb no_pos in
  (* relational constraints |y| = prod1 + prod2 *)
  (* let comb_length = CP.mkAnd rel_f comb_length0 no_pos in *)

  (* let quans = (List.map (fun (y, _, _,_) -> y) prod_vars)@ *)
  (*   (List.map (fun (_,zx) -> zx) z_vars)@ *)
  (*   (List.map (fun (_, _, zc) -> zc ) x_z_letters)in *)
  (* let r_count = CP.add_quantifiers *)
  (*   (List.fold_left (fun r e -> r@(Exp.fv e)) [] quans) comb_length in *)
  (* r_count *)
  comb_length

let cfg2parikh alphabet vars prods (x_z_letters, z_vars, prod_vars) f2 (* rel_f *) sv=
  let pr1 = pr_list Exp.string_of in
  let pr2 = pr_list Var.string_of in
  let pr3 = pr_list (pr_pair Var.string_of Exp.string_of) in
  Debug.no_4 "cfg2parikh" pr1 pr2 pr3 Var.string_of
      Cpure.string_of
      (fun _ _ _ _ -> cfg2parikh_x alphabet vars prods
          (x_z_letters, z_vars, prod_vars) f2 (* rel_f *) sv)
      alphabet vars prods sv

(*************************************************************)
(*************************************************************)
(*                   END PARIKH                              *)
(*************************************************************)
(*************************************************************)

(*************************************************************)
(*************************************************************)
(*                          CFG                              *)
(*************************************************************)
(*************************************************************)
let rec aux_rename_svs sv0 connected_sv cycles (done_cycles,acc_prods)=
  match cycles with
    | [] ->
          (* let last_sv = (Var.fresh_var sv) in *)
          (done_cycles,acc_prods, [(sv0, connected_sv)])
    | ((c, h), (ids, edges, vars))::rest ->
          let sst =
            (* first cycle is the same sv, do not need to subt *)
            if Var.equal sv0 connected_sv then [] else
              [(sv0,connected_sv)]
          in
          let n_c = E.subst sst c in
          let n_edges = List.map (E.subst sst) edges in
          let n_vars =List.map (Var.subst sst) vars in
          let next_sv = (Var.fresh_var sv0) in
          let () = Debug.ninfo_hprint(add_str "\ncycle.next_sv:\n" (  Var.string_of)) next_sv no_pos in
          aux_rename_svs sv0 next_sv rest (done_cycles@[((n_c, h), (ids, n_edges, n_vars))],acc_prods@[(sv0, Exp.Var (next_sv, no_pos))])

(* ouput: renamned cycles + extra connected productions *)
let aux_rename_cycle sv cycles=
  let inter_cycles, rest = List.partition
    ( fun (_, (ids, edges, vars)) ->
        BList.mem_eq Var.equal sv vars
    ) cycles in
  (* if any label has more than one rule*)
  if List.exists ( fun (c, (ids, edges, vars)) ->
      List.exists (fun e -> List.length e.E.label > 1) edges
  ) inter_cycles then
    None
  else
    (* sort cycles *)
    let sorted_cycles = List.sort ( fun ((_, h1), _) ((_, h2), _) ->
        h1-h2
    ) inter_cycles in
    let renamed_cycles, prods, subst_non_cycle =
      if sorted_cycles == [] then
        sorted_cycles,[], []
      else aux_rename_svs sv sv sorted_cycles ([],[])
    in
    Some (renamed_cycles@rest, prods, subst_non_cycle)


let tree2cfg_solution_trace_x tree alphabet cycle_traces
      (ids, eds, svl)=
  (************************)
    (* rename vars in multiple-cycles of each var *)
  let rec interate svl cycles acc_connect_prods acc_non_cycle_sst=
    match svl with
      | [] -> Some (cycles, acc_connect_prods,acc_non_cycle_sst)
      | sv::rest -> begin
          let r_opt = aux_rename_cycle sv cycles in
          match r_opt with
            | None -> None
            | Some (renamed_cycles, prods, non_cycle_sst) ->
                  interate rest renamed_cycles (acc_connect_prods@prods)
                      (acc_non_cycle_sst@non_cycle_sst)
        end
    in
  (************************)
  (*companion of cycle intersects with one node in the trace*)
  let inter_cycles = List.filter (fun ((e,_), _) ->
      List.exists (fun id -> id = e.E.to_id) ids
  ) cycle_traces in
    let r_opt = interate svl inter_cycles (*cycle_traces*) [] [] in
    match r_opt with
      | None -> None
      | Some (renamed_cycles, acc_connect_prods,acc_non_cycle_sst)->
            (* rename non_cycle *)
            (* let n_eds = List.map (E.subst acc_non_cycle_sst) eds in *)
            let non_cycl_prods = List.fold_left (fun r e ->
                let n_label = List.map (fun ((sv1, t1)) ->
                    let sv11 = Var.subst acc_non_cycle_sst sv1 in
                    let t11 = Exp.subst acc_non_cycle_sst t1 in
                    (sv11, t11)
                ) e.E.label in
                r@n_label
            ) [] eds in
            let cyc_prods = List.fold_left (fun r ((c,_), (_, eds,_ )) ->
                r@c.E.label@(List.fold_left (fun r1 e1 -> r1@e1.E.label) [] eds)
            ) [] renamed_cycles in
            let new_svl = List.fold_left (fun r (sv, e) ->
                r@[sv]@(Exp.fv e)
            ) [] (cyc_prods@non_cycl_prods) in
            Some (alphabet, Var.remove_dups (svl@new_svl),
            cyc_prods@acc_connect_prods@non_cycl_prods)

let tree2cfg_solution_trace tree alphabet cycle_traces
      (ids, eds, svl)=
  let pr1 = pr_list string_of_int in
  let pr2 = pr_list E.string_of in
  let pr3 = pr_list Var.string_of in
  let pr4 = pr_triple pr1 pr2 pr3 in
  let pr5 = pr_list (pr_pair Var.string_of Exp.string_of) in
  let pr6 = pr_option (pr_triple (pr_list Exp.string_of) pr3 pr5) in
  Debug.no_1 "tree2cfg_solution_trace" pr4 pr6
      (fun _ -> tree2cfg_solution_trace_x tree alphabet cycle_traces
      (ids, eds, svl)) (ids, eds, svl)

(*
 for each free var v, add productions
  v -> \semp | cv forall c in the alphabet
*)
let exlicate_free_vars_x (alphabet, vars, prods)=
  let non_free_svl = List.fold_left (fun acc (sv, _) -> acc@[sv]) [] prods in
  let free_svl = Gen.BList.difference_eq Var.equal vars non_free_svl in
  if free_svl == [] then
    prods
  else
     let () = Debug.ninfo_hprint(add_str "\ncfg" (pr_list Var.string_of))
       free_svl no_pos in
     let semp = Exp.mkEmpCConst no_pos in
     let aux_prods = List.fold_left ( fun acc sv ->
         let esv = Exp.mkVar sv no_pos in
         let cyc_prods = List.map (fun cletter ->
             let body = Exp.mkConcatExp cletter esv no_pos in
             (sv, body)
         ) alphabet in
         acc@[(sv, semp)]@cyc_prods
     ) [] free_svl in
    prods@aux_prods

let exlicate_free_vars (alphabet, vars, prods)=
  let pr1 = pr_list Var.string_of in
  let pr2 = pr_list (pr_pair Var.string_of Exp.string_of) in
  let pr3 = (pr_triple (pr_list Exp.string_of) pr1 pr2) in
  Debug.no_1 "exlicate_free_vars" pr3 pr2
      (fun _ -> exlicate_free_vars_x (alphabet, vars, prods))
      (alphabet, vars, prods)

(*************************************************************)
(*************************************************************)
(*                      END CFG                              *)
(*************************************************************)
(*************************************************************)

let elim_const_quans_x p quans=
  let elim_conj conj =
    let conjs = Cpure.split_conjunctions conj in
    let const_svs = List.fold_left (fun acc p ->
        acc@(Cpure.get_const_var p)
    ) [] conjs in
    let const_quans = Var.intersect quans const_svs in
    let f = CP.add_quantifiers const_quans conj in
    simplify_fnc f
  in
  let disjs = Cpure.split_disjunctions p in
  let disjs0 = List.map elim_conj disjs in
  Cpure.join_disjunctions disjs0

let elim_const_quans p quans=
  let pr1 = Cpure.string_of in
  let pr2 = Var.string_of_list in
  Debug.no_2 "elim_const_quans" pr1 pr2 pr1
      (fun _ _ -> elim_const_quans_x p quans) p quans

let check_sat_parikh_one_solution_trace tree alphabet cycle_traces
      sat_leaves arith a_svl (ids, eds, svl)=
  (* tree2cfg *)
  let r_opt = tree2cfg_solution_trace tree alphabet cycle_traces
      (ids, eds, svl) in
  match r_opt with
    | Some (alphabet, vars, prods0) ->
          let pr_cfg = (pr_triple (pr_list Exp.string_of) (pr_list Var.string_of)
              (pr_list (pr_pair Var.string_of Exp.string_of))) in
          let () = Debug.ninfo_hprint(add_str "cfg" (pr_cfg)) (alphabet, vars, prods0) no_pos in
          let prods =  exlicate_free_vars (alphabet, vars, prods0) in
          (* cfg2parikh *)
          (* generate aux variables *)
          let (x_z_letters, z_vars, prod_vars(* , map_var_prods *)) = cfg2parikh_aux_vars
            alphabet vars prods (* a_svl *) in
          (* let () = Debug.info_hprint(add_str "map_var_prods" (pr_list (pr_pair Var.string_of Cpure.string_of))) map_var_prods no_pos in *)
          (* 2nd component is the same for all vars *)
          let f2 = cfg2parik_2nd_component alphabet vars prods (x_z_letters, z_vars, prod_vars) in

          (*add quantifiers*)
          let quans = (List.map (fun (_,zx) -> zx) z_vars)@
            (List.map (fun (_, _, zc) -> zc ) x_z_letters)
          in

          let count_quans = List.fold_left (fun r (_, xc, _) ->
              r@(Exp.fv xc)
          ) [] x_z_letters  in
    
          let prod_quans = List.fold_left (fun acc (y, _, _,_) ->
              acc@(Exp.fv y)) [] prod_vars in
          let a_we = List.map (fun sv ->
              let f_bare = cfg2parikh alphabet vars prods (x_z_letters, z_vars, prod_vars)
                f2 sv in
              let r_count = CP.add_quantifiers
                (List.fold_left (fun r e -> r@(Exp.fv e)) [] quans) f_bare in
              let f = (* Tpdispatcher.pairwisecheck (simplify_fnc r_count) *) r_count in
              let () = Debug.ninfo_hprint(add_str "count" (Cpure.string_of)) f no_pos in
              (* let f1 = elim_const_quans f prod_quans in *)
              let f1 = f in
              let () = Debug.ninfo_hprint(add_str "f1 (after remove const)" (Cpure.string_of)) f1 no_pos in
              let f2 = CP.add_quantifiers (count_quans@prod_quans) f1 in
              let () = Debug.ninfo_hprint(add_str "f2" (Cpure.string_of)) f2 no_pos in
              f2
          ) a_svl
          in
          (* add relational constraints *)
          (* let start_sv = (List.hd a_svl) in *)
          (* let rel_f = List.fold_left (fun acc (sv, p) -> *)
          (*     if Var.eq_var sv start_sv then acc else *)
          (*       Cpure.mkAnd acc p no_pos *)
          (* ) (Cpure.mkTrue no_pos) map_var_prods in *)
          (* let f = cfg2parikh alphabet vars prods (x_z_letters, z_vars, prod_vars) *)
          (*   f2 rel_f start_sv in *)
          (* let a_we = [simplify_fnc f] in *)


          let quan_f = List.fold_left (fun r p ->
              CP.mkAnd r p no_pos
          ) (List.hd a_we) ((List.tl a_we)) in
          (* let quan_f = (\* simplify_fnc *\) (CP.add_quantifiers prod_quans f) in *)
          let () = Debug.ninfo_hprint(add_str "quan_f" (Cpure.string_of)) quan_f no_pos in
          let f = List.fold_left (fun r p ->
              CP.mkAnd r p no_pos
          ) quan_f arith in

          let r = is_sat_fnc f in
          if r = true then Out.SAT,[] else
            Out.UNSAT, []
    | None -> Out.UNKNOWN, []

let check_sat_parikh_solution_traces tree cycle_traces
      sat_leaves arith a_svl  acylic_traces=
  let rec helper alphabet ac_traces unk_traces=
    match ac_traces with
      | [] -> if unk_traces == [] then Out.UNSAT, [] else
          Out.UNKNOWN, []
      | t::rest -> let res, cex = check_sat_parikh_one_solution_trace
        tree alphabet cycle_traces sat_leaves arith a_svl t in
      if res == Out.SAT then (res, cex)
      else let n_unk_traces =
        if res == Out.UNKNOWN then
          unk_traces@[t]
        else unk_traces
      in helper alphabet rest n_unk_traces
  in
  let root = tree#get_root () in
  let alphabet = Term.get_cconst root.N.data.ENTRY.ew in
  let () = Debug.ninfo_hprint(add_str "\nalphabet:\n" (pr_list  Exp.string_of)) alphabet no_pos in
  helper alphabet acylic_traces []

let get_trace_vars tree (ids, edges)=
  match ids with
    | [] -> []
    | comp_id::_ ->
          let n = tree#get_node comp_id in
          let comp_svs = Var.remove_dups
           (Term.fv n.N.data.ENTRY.ew) in
          (* get label vars *)
          let label_svs = List.fold_left (fun r e ->
              let new_svs = List.fold_left (fun r (_, e) ->
                  r @ (Exp.fv e)
              ) [] e.E.label in
              r@new_svs
          ) [] edges in
          Var.remove_dups (comp_svs@label_svs)

let check_sat_parikh tree sat_leaves arith a_svl=
  let () = Debug.ninfo_hprint(add_str "\nArith:\n" (pr_list  Cpure.string_of)) arith no_pos in
  (* get non-cycle-traces *)
  let non_cycle_traces = List.map tree # build_non_cycle_trace sat_leaves in
  let pr_acyclic_trace = pr_triple (pr_list string_of_int)
    (pr_list E.string_of) (pr_list Var.string_of) in
  let () = Debug.ninfo_hprint(add_str "\nNonCycle Traces:\n"  (pr_list  pr_acyclic_trace)) non_cycle_traces no_pos in
  (* get cycle-traces *)
  let cycle_traces = tree # build_cycle_traces () in
  (* get VAR *)
  let cycle_traces_vars = List.map (fun (c, (ids, edges)) ->
      let () = Debug.ninfo_hprint(add_str "\nCycle Traces:\n"  (E.string_of)) c no_pos in
      (* added vars *)
      let vars = get_trace_vars tree (ids, edges) in
      (* added distance to root from comp *)
      let h = tree#get_height c.E.to_id in
      ((c, h), (ids, edges, vars))
  ) cycle_traces in
  let pr_trace = pr_pair (pr_pair E.string_of string_of_int)
    (pr_triple (pr_list string_of_int) (pr_list E.string_of)
        (pr_list Var.string_of)) in
  let () = Debug.ninfo_hprint(add_str "\nCycle Traces:\n"  (pr_list  pr_trace)) cycle_traces_vars no_pos in

  (* check sat for each solution trace *)
  check_sat_parikh_solution_traces tree cycle_traces_vars
      sat_leaves arith a_svl non_cycle_traces
