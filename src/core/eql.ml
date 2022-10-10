(*
this module handles (dis)eq logic
*)

open Globals
open Gen
open VarGen


module CP = Cpure
module CT = Term
module E = Exp
module V = Var

type t = {
    qvars : V.t list;
    eqs : (V.t * V.t) list;
    diseqs : (V.t * V.t) list;
    null_vars : V.t list;
    disnull_vars : V.t list;
    is_poss_sat : bool;
}

let string_of_eq (sv1, sv2) =
  (V.string_of sv1) ^ "=" ^ (V.string_of sv2)

let string_of_eqs = pr_lst "&" string_of_eq

let string_of_diseq (sv1, sv2) =
  (V.string_of sv1) ^ "!=" ^ (V.string_of sv2)

let string_of_diseqs = pr_lst "&" string_of_diseq

let string_of_null_vars =
  let string_of_null_var sv = (V.string_of sv) ^ "=" ^"null" in
  pr_lst "&"  string_of_null_var

let string_of_disnull_vars =
  let string_of_disnull_var sv = (V.string_of sv) ^ "!=" ^ "null" in
  pr_lst "&"  string_of_disnull_var

let string_of f=
  let ex = if f.qvars = [] then   "" else "Ex " ^ (V.string_of_list f.qvars) ^ ". " in
  let eq_str = if f.eqs !=[] then
    (string_of_eqs f.eqs) ^ " & "
  else "" in
  let diseqs_str = if f.diseqs != [] then
    (string_of_diseqs f.diseqs)  ^ " & "
  else "" in
  let null_vars_str = if f.null_vars != [] then
    (string_of_null_vars f.null_vars) ^ " & "
  else "" in
  ex ^ eq_str  ^ diseqs_str  ^ null_vars_str ^
      (string_of_disnull_vars f.disnull_vars) ^ "\n" ^
      "status: " ^ (string_of_bool f.is_poss_sat)

let decompose f= (f.null_vars, f.disnull_vars, f.eqs, f.diseqs)

let eq_x t1 t2=
  List.length t1.eqs == List.length t2.eqs &&
      List.length t1.diseqs == List.length t2.diseqs &&
      List.length t1.null_vars == List.length t2.null_vars &&
      List.length t1.disnull_vars == List.length t2.disnull_vars &&
      List.for_all (fun v1 -> List.exists (fun v2 -> Var.equal v1 v2) t2.null_vars) t1.null_vars
      &&
      (* Var.diff t1.disnull_vars t2.disnull_vars == [] *)
      List.for_all (fun v1 -> List.exists (fun v2 -> Var.equal v1 v2) t2.disnull_vars) t1.disnull_vars
      &&
      (* Gen.BList.difference_eq Var.equal_pair_vars t1.eqs t2.eqs == [] *)
      List.for_all (fun pr1 -> List.exists (fun pr2 -> Var.equal_pair_vars pr1 pr2) t2.eqs) t1.eqs
      &&
      (* Gen.BList.difference_eq Var.equal_pair_vars t1.diseqs t2.diseqs == [] *)
       List.for_all (fun pr1 -> List.exists (fun pr2 -> Var.equal_pair_vars pr1 pr2) t2.diseqs) t1.diseqs

let eq t1 t2=
  Debug.no_2 "EQL.eq" string_of string_of string_of_bool
      (fun _ _ -> eq_x t1 t2) t1 t2

let fv f=
  let eq_vs = List.fold_left (fun r (sv1,sv2) -> r@[sv1;sv2] ) [] f.eqs in
  let r2 = List.fold_left (fun r (sv1,sv2) -> r@[sv1;sv2] ) eq_vs f.diseqs in
  V.remove_dups (r2@f.null_vars@f.disnull_vars)

let subst sst f=
  if not f.is_poss_sat then f else
    let n_eqs = List.fold_left (fun r (sv1, sv2)->
        let n_sv1 = V.subst sst sv1 in
        let n_sv2 = V.subst sst sv2 in
        if V.equal n_sv1 n_sv2 then r else r@[(n_sv1, n_sv2)]
    ) [] f.eqs in
    let is_not_sat, n_diseqs = List.fold_left (fun (r_b,r) (sv1, sv2)->
        let n_sv1 = V.subst sst sv1 in
        let n_sv2 = V.subst sst sv2 in
        if V.equal n_sv1 n_sv2 then (false, r@[(n_sv1, n_sv2)])
        else (r_b,r@[(n_sv1, n_sv2)])
    ) (true, []) f.diseqs in
    let n_null_vars = List.map (fun sv -> V.subst sst sv) f.null_vars in
    let n_disnull_vars = List.map (fun sv -> V.subst sst sv) f.disnull_vars in
    { f with eqs = n_eqs; diseqs = n_diseqs;
        null_vars = n_null_vars; disnull_vars = n_disnull_vars;
        is_poss_sat = f.is_poss_sat&&is_not_sat&&(V.intersect n_null_vars n_disnull_vars == [])
    }

let mk_diseq (sv1,sv2)=
  if V.equal sv1 sv2 then
    (false, (sv1, sv2))
  else (true, (sv1, sv2))

let mk_diseqs diseqs=
  List.fold_left (fun (acc_sat, acc) (sv1,sv2)->
      let is_poss_sat, neq = mk_diseq (sv1, sv2) in
      acc_sat&&is_poss_sat, acc@[(sv1,sv2)]
  ) (true, []) diseqs

let mkAnd_eqs f eqs=
  {f with eqs = f.eqs@eqs;
  }

let mkAnd_diseqs f diseqs=
  let is_poss_sat = List.fold_left (fun acc (sv1,sv2)->
      if V.equal sv1 sv2 then false else acc
  ) f.is_poss_sat diseqs in
  {f with diseqs = f.diseqs@diseqs;
      is_poss_sat =  is_poss_sat;
  }

let mkAnd_disnull f disnull_vars=
  let null_vars = f.null_vars in
  let is_poss_sat = List.for_all (fun v1 ->
      List.for_all (fun v2 ->
          not (V.equal v1 v2)) null_vars
  ) disnull_vars in
  {f with disnull_vars = f.disnull_vars@disnull_vars;
      is_poss_sat = f.is_poss_sat && is_poss_sat;
  }

let is_poss_sat_null null_vars disnull_vars=
  if null_vars == [] || disnull_vars == [] then true
  else
    List.for_all (fun v1 ->
        List.for_all (fun v2 -> not(V.equal v1 v2)) null_vars
    ) disnull_vars


let subst_one (sv1, sv2) f=
  if not f.is_poss_sat then f else
  let subst_var = V.subst [(sv1,sv2)] in
  let n_qvars = if V.mem sv1 f.qvars then V.diff f.qvars [sv1] else f.qvars in
  let n_eqs = List.fold_left (fun acc (sv3, sv4) ->
      let n_sv3 = subst_var sv3 in
      let n_sv4 = subst_var sv4 in
      if V.equal n_sv3 n_sv4 then
        acc
      else acc@[(n_sv3, n_sv4)]
  ) [] f.eqs in
  let n_diseqs = List.map (fun (sv3, sv4) -> (subst_var sv3, subst_var sv4) ) f.diseqs in
  let n_null_vars = Var.remove_dups (List.map (fun sv3 -> subst_var sv3) f.null_vars) in
  let n_disnull_vars = Var.remove_dups (List.map (fun sv3 -> subst_var sv3) f.disnull_vars) in
  let is_poss_sat1 = if List.exists (fun (sv3, sv4) -> V.equal sv3 sv4) n_diseqs then
    false
  else is_poss_sat_null n_null_vars n_disnull_vars in
  {qvars = n_qvars;
  eqs = n_eqs;
  diseqs = n_diseqs;
  null_vars = n_null_vars;
  disnull_vars = n_disnull_vars;
  is_poss_sat = is_poss_sat1;
  }

(*
eliminate equalities,
 ex x. x = y => f[y/x],[x]
 x=y, => f[y/x], []
*)
let elim_eq_x f=
  let rec helper arr_eqs elim_qvars uni_elim_eqs f_cur =
    match f_cur.eqs with
      | (sv1,sv2)::rest ->
            let f_cur1 = {f_cur with eqs = rest} in
            let arr_eqs1, elim_qvars1, uni_elim_eqs1, f_n =
              if V.mem sv1 f_cur.qvars  then
                (arr_eqs@[(sv1,sv2)], elim_qvars@[sv1], uni_elim_eqs, subst_one (sv1, sv2) f_cur1)
              else if V.mem sv2 f_cur.qvars then
                (arr_eqs@[(sv2,sv1)], elim_qvars@[sv2], uni_elim_eqs, subst_one (sv2, sv1) f_cur1)
              else (arr_eqs@[(sv1,sv2)], elim_qvars, uni_elim_eqs@[(sv1,sv2)], subst_one (sv1, sv2) f_cur1)
            in helper arr_eqs1 elim_qvars1 uni_elim_eqs1 f_n
      | [] -> (arr_eqs, elim_qvars, uni_elim_eqs, f_cur)
  in
  (* let eqs = f.eqs in *)
  (* let elimed_svs, f1 = List.fold_left (fun (acc_svs,acc_f) (sv1,sv2) -> *)
  (*     acc_svs@[sv1], subst_one (sv1, sv2) f *)
  (* ) ([],f) eqs in *)
  (*  elimed_svs, {f1 with eqs = []} *)
  (* let f1 = {f with eqs = Var.to_parallel_subst f.eqs} in *)
  helper [] [] [] f

let elim_eq f=
  let pr1 = (pr_list V.string_of_pair) in
  let pr_out =  pr_quad pr1 V.string_of_list pr1 string_of in
  Debug.no_1 "EQL.elim_eq" string_of pr_out
      (fun _ -> elim_eq_x f) f

let expand_closure f =
  let eqnulls = Var.get_eq_closure f.eqs f.null_vars in
  let diseqnulls = Var.get_eq_closure f.eqs f.disnull_vars in
  {f with null_vars = eqnulls;
      disnull_vars = diseqnulls;
  }

let elim_ex_qvars_x vs f=
  if vs == [] || not f.is_poss_sat then vs, f
  else begin
    if f.eqs == [] then
      let n_diseqs = List.filter (fun (v1,v2) ->
          not (V.mem v1 vs || V.mem v2 vs)
      ) f.diseqs in
      let n_qvars = V.diff f.qvars vs in
      n_qvars, {f with qvars = n_qvars;
          diseqs = n_diseqs;
          null_vars = V.diff f.null_vars vs;
          disnull_vars = V.diff f.disnull_vars vs;
      }
    else vs, f
  end

let elim_ex_qvars vs f=
  Debug.no_2 "EQL.elim_ex_quan" Var.string_of_list string_of (pr_pair Var.string_of_list string_of)
      (fun _ _ -> elim_ex_qvars_x vs f) vs f

(* let ex_null_x f= *)
(*   let null_qvars = Var.intersect f.qvars f.null_vars in *)
(*   if null_qvars == [] then f else *)
(*     let n_neqs, n_disnullvars = List.fold_left (fun (r1, r2) (sv1, sv2) -> if Var.mem sv2 null_qvars then *)
(*       (r1, r2@[sv1]) *)
(*     else if Var.mem sv1 null_qvars then *)
(*       (r1, r2@[sv2]) *)
(*     else (r1@[(sv1,sv2)], r2) *)
(*     ) ([], []) f.diseqs in *)
(*     {f with diseqs = n_neqs; *)
(*         disnull_vars = f.disnull_vars@n_disnullvars *)
(*     } *)

(* let ex_null f= *)
(*   Debug.no_1 "EQL.ex_null" string_of string_of *)
(*       (fun _ -> ex_null_x f) f *)

let mk qvars null_vars disnull_vars eqs diseqs=
  let is_poss_sat1, diseqs = mk_diseqs diseqs in
  let is_poss_sat2 = is_poss_sat_null null_vars disnull_vars in
  let eql_f = {
      qvars = qvars;
      eqs = eqs;
      diseqs = diseqs;
      null_vars = null_vars;
      disnull_vars =disnull_vars;
      is_poss_sat = is_poss_sat1&&is_poss_sat2;
  } in
  (* elim_ex_quan *) eql_f

let mkFalse () =
  {
      qvars = [];
      eqs = [];
      diseqs = [];
      null_vars = [];
      disnull_vars = [];
      is_poss_sat = false;
  }

let to_pure f=
  if not f.is_poss_sat then
    CP.mkFalse no_pos
  else
    let f1 = List.fold_left (fun acc_p (sv1, sv2) ->
        let p = CP.mkEqExp (E.mkVar sv1 no_pos) (E.mkVar sv2 no_pos) no_pos in
        CP.mkAnd acc_p p no_pos
    ) (CP.mkTrue no_pos) f.eqs in
    let f2 = List.fold_left (fun acc_p (sv1, sv2) ->
        let p = CP.mkNeqExp (E.mkVar sv1 no_pos) (E.mkVar sv2 no_pos) no_pos in
        CP.mkAnd acc_p p no_pos
    ) f1 f.diseqs in
    let eNull = E.Null no_pos in
    let f3 = List.fold_left (fun acc_p sv1 ->
        let p = CP.mkEqExp (E.mkVar sv1 no_pos) eNull no_pos in
        CP.mkAnd acc_p p no_pos
    ) f2 f.null_vars in
    List.fold_left (fun acc_p sv1 ->
        let p = CP.mkNeqExp (E.mkVar sv1 no_pos) eNull no_pos in
        CP.mkAnd acc_p p no_pos
     ) f3 f.disnull_vars

let check_sat_over f0=
  if not f0.is_poss_sat then
    Out.UNSAT
  else
    Out.UNKNOWN

let remove_dups f0=
  if not f0.is_poss_sat then
    f0
  else
    {f0 with null_vars = V.remove_dups f0.null_vars;
        disnull_vars = V.remove_dups f0.disnull_vars;
        eqs = BList.remove_dups_eq V.equal_pair_vars f0.eqs;
        diseqs = BList.remove_dups_eq V.equal_pair_vars f0.diseqs;
    }

let check_sat f0=
  if not f0.is_poss_sat then
    Out.UNSAT
  else
    let rec aux f=
      match f.eqs with
        | [] -> Out.SAT
        | (sv1,sv2)::rest -> if Var.equal sv1 sv2 then
            aux {f with eqs = rest}
          else
            let f1 = subst_one (sv1, sv2) f in
            let () = Debug.ninfo_hprint (add_str  "f"  string_of) f no_pos in
     let () = Debug.ninfo_hprint (add_str  "f1"  string_of) f1 no_pos in
            if List.exists (fun (sv3, sv4) -> V.equal sv3 sv4 ||
                ((List.exists (fun v1 -> Var.equal v1 sv3) f1.null_vars ) && (List.exists (fun v1 -> Var.equal v1 sv4) f1.null_vars))
            ) f1.diseqs then
              Out.UNSAT
            else if not (is_poss_sat_null f1.null_vars f1.disnull_vars) then
              Out.UNSAT
            else aux f1
    in aux f0

let is_top_x f0=
  if not f0.is_poss_sat then
    false
  else f0.eqs==[] && f0.diseqs == [] &&
    f0.null_vars == [] && f0.disnull_vars == []

let is_top f0=
  Debug.no_1 "EQ.is_top" string_of string_of_bool
      (fun _ -> is_top_x f0) f0

let hypo ante cons=
  if not cons.is_poss_sat then cons
  else
    let eq_null_svs, cons_eqs = List.fold_left (fun (r1,r2) (sv1, sv2) ->
        if Var.equal sv2 Var.null_var then
          (r1@[sv2], r2)
        else (r1,r2@[(sv1,sv2)])
    ) ([], []) cons.eqs in
    let n_null =  V.diff (cons.null_vars@eq_null_svs) ante.null_vars in
    let n_disnull = V.diff cons.disnull_vars ante.disnull_vars in
    let n_diseqs = List.filter (fun (sv1, sv2) ->
        not (List.exists (fun (sv3, sv4) ->
            ( V.equal_pair_vars (sv1, sv2) (sv3, sv4)))
            ante.diseqs)
        && not (Var.mem sv1 ante.disnull_vars && Var.mem sv2 ante.null_vars)
    ) cons.diseqs in
    {cons with null_vars = n_null;
        disnull_vars = n_disnull;
        diseqs = n_diseqs;
        eqs = cons_eqs;
    }

let mkAnd_x f1 f2=
  if not f1.is_poss_sat then f1
  else if not f2.is_poss_sat then f2
  else
    let qvars = V.remove_dups (f1.qvars@f2.qvars) in
    let eqs = f1.eqs@f2.eqs in
    let diseqs = f1.diseqs@f2.diseqs in
    let null_vars = V.remove_dups (f1.null_vars@f2.null_vars) in
    let disnull_vars = V.remove_dups (f1.disnull_vars@f2.disnull_vars) in
    let is_poss_sat = if List.exists (fun (sv3, sv4) -> V.equal sv3 sv4) diseqs then
      false
    else is_poss_sat_null null_vars disnull_vars
    in
    {qvars = qvars;
    eqs = eqs;
    diseqs = diseqs;
    null_vars = null_vars;
    disnull_vars = disnull_vars;
    is_poss_sat = is_poss_sat;
    }

let mkAnd f1 f2=
  Debug.no_2 "EQL.mkAnd" string_of string_of string_of
      (fun _ _ -> mkAnd_x f1 f2) f1 f2

let elim_ex_null_var f=
  if not f.is_poss_sat then [],[], f
  else
    let null_qvars, qvars = List.partition (fun sv ->
        Var.mem sv f.null_vars) f.qvars in
    if null_qvars==[] then
      [], [], f
    else
      let sst = List.map (fun sv ->
          (sv, Var.null_var)) null_qvars in
      let n_f = { f with qvars = Var.diff f.qvars null_qvars;
          eqs = List.map (fun (sv1,sv2)-> (Var.subst sst sv1, Var.subst sst sv2) ) f.eqs;
          diseqs = List.map (fun (sv1,sv2)-> (Var.subst sst sv1, Var.subst sst sv2) ) f.diseqs;
          null_vars = (Var.diff f.null_vars null_qvars);
          disnull_vars =  List.map (Var.subst sst) f.disnull_vars;
      } in
      null_qvars, sst, n_f
