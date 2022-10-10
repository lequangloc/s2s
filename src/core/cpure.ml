open Globals
open VarGen
open Gen

open Term
open Exp
open Var

type formula =
  | BForm of Term.t
  | Not of formula
  | Exists of (var * formula)
  | Forall of (var * formula)
  | And of (formula * formula)
  | Or of (formula * formula)

type t = formula

type relation = (* for obtaining back results from Omega Calculator. Will see if it should be here *)
  | ConstRel of bool
  | BaseRel of (Exp.t list * t)
  | UnionRel of (relation * relation)

and constraint_rel =
  | Unknown
  | Subsumed
  | Subsuming
  | Equal
  | Contradicting


let rec string_of conj=
  match conj with
    | BForm f -> Term.string_of f
    | Not p1 -> "not(" ^ (string_of p1) ^ ")"
    | Exists (sv, p1) -> "exists " ^ (Var.string_of sv) ^ ": " ^ (string_of p1)
    | Forall (sv, p1) -> "forall " ^ (Var.string_of sv) ^ ": " ^ (string_of p1)
    | And (f1, f2) -> (string_of f1) ^ " & " ^ (string_of f2)
    | Or (f1, f2) -> "("^(string_of f1) ^ " || " ^ (string_of f2)^")"

let rec split_conjunctions f= match f with
  | And (f1, f2) -> (split_conjunctions f1)@(split_conjunctions f2)
  | _ -> [f]

let rec is_string_form f = match f with
  | BForm t ->  Term.is_string_term t
  | Not f -> is_string_form f
  | Exists (_, f) -> is_string_form f
  | Forall (_, f) -> is_string_form f
  | And (f1, f2) | Or (f1, f2)  -> (is_string_form f1) && (is_string_form f2)

let rec is_arith_form f= match f with
  | BForm t ->  Term.is_arith_term t
  | Not f -> is_arith_form f
  | Exists (_, f) -> is_arith_form f
  | Forall (_, f) -> is_arith_form f
  | And (f1, f2) | Or (f1, f2)  -> (is_arith_form f1) && (is_arith_form f2)


let rec is_simple_word_equation f = match f with
  | BForm t ->  Term.is_simple_word_equation t
  | Not _ -> false
  | Exists _ | Forall _
  | And _ | Or _ -> false


let rec fv f =
  let tmp = fv_helper f in
  let res = Var.remove_dups tmp in
  res

and all_vars_helper (f : formula) : Var.t list = match f with
  | BForm t -> Term.fv t
  | And (p1, p2) -> combine_pvars p1 p2 all_vars_helper
  | Or (p1, p2 (*, _ ,_ *)) -> combine_pvars p1 p2 all_vars_helper
  | Not (nf) -> all_vars_helper nf
  | Forall (qid, qf)
  | Exists (qid, qf) -> qid::(all_vars_helper qf) 

and fv_helper (f : formula) :  Var.t list = match f with
  | BForm b -> Term.fv b
  | And (p1, p2) -> combine_pvars p1 p2 fv_helper
  | Or (p1, p2) -> combine_pvars p1 p2 fv_helper
  | Not (nf) -> fv_helper nf
  | Forall (qid, qf) -> remove_qvar qid qf
  | Exists (qid, qf) -> remove_qvar qid qf

and combine_pvars p1 p2 helper = (helper p1) @ (helper p2)

and all_vars (f : formula) :  Var.t list =
  let tmp = all_vars_helper f in
  let res = Var.remove_dups tmp in
  res

and remove_qvar qid qf =
  let qfv = fv_helper qf in
  Gen.BList.difference_eq Var.equal qfv [qid]


let mkTrue pos = BForm (Term.mkTrue pos)

let isTrue p = match p with
  | BForm (BConst (true, _)) -> true
  | _ -> false

let mkFalse pos = BForm (Term.mkFalse pos)

let isFalse p = match p with
  | BForm (BConst (false, _)) -> true
  | _ -> false

let mkEqExp (ae1 : Exp.t) (ae2 : Exp.t) pos :t =
  match (ae1, ae2) with
    | (Exp.Var v1, Exp.Var v2) ->
          if Var.equal (fst v1) (fst v2) then
            mkTrue pos
          else
            BForm (Term.mkEq ae1 ae2 pos)
    | _ -> BForm (Term.mkEq ae1 ae2 pos)

let mkNeqExp (ae1 : Exp.t) (ae2 : Exp.t) pos :t =
  match (ae1, ae2) with
    | (Exp.Var v1, Exp.Var v2) ->
          if Var.equal (fst v1) (fst v2) then
            mkFalse pos
          else
            BForm (Term.mkNeq ae1 ae2 pos)
    | _ -> BForm (Term.mkNeq ae1 ae2 pos)

let mkEqZeroExp (ae1 : Exp.t) pos :t =
  let ae2 = Exp.mkZero no_pos in
  mkEqExp ae1 ae2 pos

let mkGteZeroExp (ae1 : Exp.t) pos :t =
  BForm (Term.mkGteZero ae1 pos)

let mkGtZeroExp (ae1 : Exp.t) pos :t =
  BForm (Term.mkGtZero ae1 pos)

let mkEqVar (sv1 : Var.t) (sv2 : Var.t) pos =
  if Var.equal sv1 sv2 then
    mkTrue pos
  else
    BForm (Term.mkEq (Exp.mkVar sv1 pos) (Exp.mkVar sv2 pos) pos)

let mkNeqVar (sv1 : Var.t) (sv2 : Var.t) pos =
  if Var.equal sv1 sv2 then
    mkFalse pos
  else
    BForm (Term.mkNeq (Exp.mkVar sv1 pos) (Exp.mkVar sv2 pos) pos)


let mkNot p pos = Not (p)

let rec add_quantifiers qvars f0=
  match qvars with
  | [] -> f0
  | v::rest ->  add_quantifiers rest (Exists (v, f0))

let split_quantifiers f0=
  let rec aux f res=
    match f with
      | Exists (v, qf) -> aux qf (res@[v])
      | _ -> res, f
  in aux f0 []


let mkOr p1 p2 pos = Or (p1, p2)

let rec split_disjunctions =
  (* split_disjuncts *)
  function
  | Or (x, y) -> (split_disjunctions x) @ (split_disjunctions y)
  | z -> [z]

let join_disjunctions ps=
  if ps = [] then mkTrue no_pos else
    List.fold_left (fun p1 p2 -> mkOr p1 p2 no_pos) (List.hd ps)
        (List.tl ps)

let count_disj f =
  let k = split_disjunctions f
  in List.length k

let rec conj_of_list (fs : formula list) pos : formula =
  match fs with
  | [] -> mkTrue pos
  | x::xs -> List.fold_left (fun a c-> mkAnd a c no_pos) x xs

and join_conjunctions fl pos = conj_of_list fl pos

and equalFormula_f (eq:Var.t -> Var.t -> bool) (f01:t)(f02:t):bool =
  let pr = string_of in
  Debug.no_2 "equalFormula_f" pr pr string_of_bool
      (fun _ _ -> equalFormula_f_x eq f01 f02) f01 f02

(*limited, should use equal_formula, equal_b_formula, eq_exp instead*)
and equalFormula_f_x (eq:Var.t -> Var.t -> bool) (f01:t)(f02:t):bool =
  let rec helper f1 f2=
    match (f1,f2) with
    | ((BForm b1),(BForm b2)) -> Term.equalTerm eq  b1 b2
    | ((Not (b1)),(Not (b2))) -> helper b1 b2
    (* | (Or(f1, f2, _,_), Or(f3, f4, _,_)) *)
    | (And(f1, f2), And(f3, f4)) -> ((helper f1 f3) && (helper f2 f4))
          || ((helper f1 f4) && (helper f2 f3))
    | (Exists(sv1, f1), Exists(sv2, f2))
    | (Forall(sv1, f1), Forall(sv2, f2)) ->
            (eq sv1 sv2) && (helper f1 f2)
    | _ -> false
  in
  let ps1 = split_conjunctions f01 in
  let ps2 = split_conjunctions f02 in
  let l1 = List.length ps1 in
  if l1 == List.length ps2 then
    if l1<=2 then
      helper f01 f02
    else
      List.for_all (fun p2 -> List.exists (fun p1 -> helper p1 p2) ps1) ps2
  else false


and equal (f1:formula) (f2:formula):bool = equalFormula_f Var.equal f1 f2

and remove_redundant_helper ls rs=
  match ls with
  | [] -> rs
  | f::fs -> if List.exists (equal f) fs then
      remove_redundant_helper fs rs
    else (match f with
        | BForm (Eq(e1, e2, _)) -> if (Exp.eqExp_f Var.equal e1 e2) then
            remove_redundant_helper fs rs
          else remove_redundant_helper fs rs@[f]
        | BForm (Lte(IConst (0,_), IConst (0,_), _)) -> remove_redundant_helper fs rs
        | _ -> remove_redundant_helper fs rs@[f]
      )

and remove_redundant (f:formula):formula =
  let l_conj = split_conjunctions f in
  let prun_l = remove_redundant_helper l_conj [] in
  join_conjunctions prun_l no_pos

and remove_primitive should_elim e =
  let rec elim_formula f = match f with
    | BForm bf -> if (should_elim bf) then None else Some f
    | Or (f1, f2) ->
      let nf1 = elim_formula f1 in
      let nf2 = elim_formula f2 in
      (match (nf1,nf2) with
       | (None,None) -> None
       | (None,Some _) -> nf2
       | (Some _,None) -> nf1
       | (Some nff1, Some nff2) -> Some (Or (nff1, nff2)))
    | And (f1, f2) ->
      let nf1 = elim_formula f1 in
      let nf2 = elim_formula f2 in
      (match (nf1,nf2) with
       | (None,None) -> None
       | (None,Some _) -> nf2
       | (Some _,None) -> nf1
       | (Some nff1, Some nff2) -> Some (And (nff1, nff2)))
    | Forall (sv, f1) ->
          let nf = elim_formula f1 in
          (match nf with
            | None -> None
            | Some nf1 -> Some (Forall (sv, nf1)))
    | Exists (sv, f1) -> 
      let nf = elim_formula f1 in
      (match nf with
       | None -> None
       | Some nf1 -> Some (Exists (sv, nf1)))
    | Not (f1) -> 
      let nf = elim_formula f1 in
      (match nf with
       | None -> None
       | Some nf1 -> Some (Not (nf1))) in
  let r = elim_formula e in
  match r with
  | None -> mkTrue no_pos
  | Some f -> f

(* subst *)
and subst_one_term (fr, t) f = match f with
  | BForm (bf) -> BForm (Term.t_subst_one_term (fr, t) bf )
  | And (p1, p2) ->
        let n_p1 = subst_one_term (fr, t) p1 in
        let n_p2 =  subst_one_term (fr, t) p2 in
        mkAnd n_p1 n_p2 no_pos
  | Or (p1, p2(* , lbl, pos *)) -> Or (subst_one_term (fr, t) p1,
    subst_one_term (fr, t) p2(* , lbl, pos *))
  | Not (p) -> Not (subst_one_term (fr, t) p)
  | Forall (v, qf) -> if Var.equal v fr then f
    else Forall (v, subst_one_term (fr, t) qf)
  | Exists (v, qf) -> if Var.equal v fr then f else
      Exists (v, subst_one_term (fr, t) qf)

and subst sst f=
  List.fold_left (fun f0 ss -> subst_one_term ss f0)  f sst

and subst_var sst f=
  let sst_e = List.map (fun (sv1,sv2) ->
      let e = Exp.Var (sv2, no_pos) in
      (sv1, e)
  ) sst in
  subst sst_e f

and fresh_quantifiers f0=
  let rec aux f= match f with
    | Exists (v, qf) ->
          let qvar = Var.fresh_var v in
          let n_qf = aux qf in
          Exists (qvar, subst_var [(v,qvar)] n_qf)
    | _ -> f
  in aux f0

and mkAnd p1 p2 pos =
  if isTrue p1 then p2 else
    if isTrue p2 then p1 else
      let qvar1, b1 = split_quantifiers p1 in
      let qvar2, b2 = split_quantifiers p2 in
      let inter_svs = Var.intersect qvar1 qvar2 in
      let () = Debug.ninfo_hprint (add_str  "inter_svs" (Var.string_of_list)) inter_svs no_pos in
      let b21,qvar21 = if inter_svs == [] then
        b2,qvar2
      else
        let qvar22 = Var.fresh_vars qvar2 in
        let sst = List.combine qvar2 qvar22 in
        (subst_var sst b2), qvar22
      in
      add_quantifiers (qvar1@qvar21) (And (b1, b21))

let mkAnd_dumb f1 f2 pos =
  if (isFalse f1) then f1
  else if (isTrue f1) then f2
  else if (isFalse f2) then f2
  else if (isTrue f2) then f1
  else And (f1, f2)

let rec subst_type t_sst f0 =
  let rec aux f= match f with
    | BForm (bf) -> BForm (Term.subst_type t_sst bf )
    | And (p1, p2) -> And (aux p1, aux p2)
    | Or (p1, p2(* , lbl, pos *)) -> Or (aux p1, aux p2(* , lbl, pos *))
    | Not (p) -> Not (aux p)
    | Forall (v, qf) -> Forall (Var.subst_type t_sst v, aux qf)
    | Exists (v, qf) -> Exists (Var.subst_type t_sst v, aux qf)
  in aux f0



let mk_string_inv f=
  let svs = (fv f) in
  let zero = Exp.mkZero no_pos in
  let inv = List.fold_left (fun r sv ->
      let isv_id = Globals.lookup_sleng_insert sv.Var.id in
      let isv = {Var.t = Int; Var.id = isv_id;
      Var.p = sv.Var.p;
      } in
      let sv_f = BForm (Term.mkGte (Exp.mkVar isv no_pos) zero no_pos) in
      And (sv_f, r)
  ) (mkTrue no_pos) svs in
  inv


let rec string_of_relation (e:relation) : string =
  match e with
  | ConstRel b -> if b then "True" else "False"
  | BaseRel (el,f) -> pr_pair (pr_list Exp.string_of)
        string_of (el,f)
  | UnionRel (r1,r2) -> (string_of_relation r1)^"\n"^(string_of_relation r2)^"\n"

let build_relation relop alist10 alist20 pos =
  let rec helper1 ae alist =
    (* print_endline "inside helper1"; *)
    let a = List.hd alist in
    let rest = List.tl alist in
    let rec tt relop ae a pos = 
      let r = (relop ae a pos) in
      r in
    (* print_endline "before tt"; *)
    let tmp = BForm (tt relop ae a pos) in
    if Gen.is_empty rest then
      tmp
    else
      let tmp1 = helper1 ae rest in
      let tmp2 = mkAnd tmp tmp1 pos in
      tmp2 in
  let rec helper2 alist1 alist2 =
    (* print_endline "inside helper2"; *)
    let a = List.hd alist1 in
    let rest = List.tl alist1 in
    let tmp = helper1 a alist2 in
    if Gen.is_empty rest then
      tmp
    else
      let tmp1 = helper2 rest alist2 in
      let tmp2 = mkAnd tmp tmp1 pos in
      tmp2 in
  if List.length alist10 = 0 || List.length alist20 = 0 then
    failwith ("build_relation: zero-length list")
  else
    helper2 alist10 alist20

let drop_rel_formula_ops ()=
  let pr_weak b = match b with
    | Term.RelForm (_,_,p) -> Some (mkTrue p)
    | _ -> None in
  let pr_strong b = match b with
    | Term.RelForm (_,_,p) -> Some (mkFalse p)
    | _ -> None in
  (pr_weak,pr_strong)

let rec drop_formula (pr_w:Term.t -> formula option)
      pr_s (f:formula) : formula =
  let rec helper f = match f with
    | BForm b -> 
      (match pr_w b with
       | None -> f
       | Some nf -> nf)
    | And (f1,f2) -> And (helper f1,helper f2)
    | Or (f1,f2) -> Or (helper f1,helper f2)
    | Exists (vs,f) -> Exists (vs, helper f)
    | Not (f) -> Not (drop_formula pr_s pr_w f)
    | Forall (vs,f) -> Forall (vs, helper f)
  in helper f

let drop_rel_formula (f:t) : t =
  let (pr_weak,pr_strong) = drop_rel_formula_ops () in
  drop_formula pr_weak pr_strong f

let is_update_array_relation (r:string) = 
  (* match r with CP.SpecVar(_,r,_) -> *)
  let udrel = "update_array" in
  let udl = String.length udrel in
  (String.length r) >= udl && (String.sub r 0 udl) = udrel


let drop_complex_ops ()=
  let pr_weak b = match b with
    (* | LexVar t_info -> Some (mkTrue t_info.lex_loc) *)
    | Term.RelForm (sv,_,p) ->
          let v = sv (* sv.Var.id *) in
          (*provers which can not handle relation => throw exception*)
          if (v="dom") || (v="amodr") || (is_update_array_relation v) then None
          else Some (mkTrue p)
    | _ -> None in
  let pr_strong b = match b with
    (* | LexVar t_info -> ((\*print_string "dropping strong1\n";*\)Some (mkFalse t_info.lex_loc)) *)
    | Term.RelForm (sv,_,p) ->
          let v = sv(* .Var.id *) in
          (*provers which can not handle relation => throw exception*)
          if (v="dom") || (v="amodr") || (is_update_array_relation v) then None
          else Some (mkFalse p)
    | _ ->  None in
  (pr_weak,pr_strong)

let memo_complex_ops stk bool_vars is_complex =
  let pr b = match b with
    | BVar(v,_) -> bool_vars # push v; None
    | _ ->
      if (is_complex b) then
        let id = fresh_old_name "memo_rel_hole_" in
        let v = Var.mk Bool id Unprimed in
        let rel_f = BForm b in
        stk # push (v,rel_f);
        Some (BForm (BVar (v,no_pos)))
      else None
  in (pr, pr)

let memoise_formula_ho is_complex (f:formula) : 
  (formula * ((Var.t * formula) list) * (Var.t list)) =
  let stk = new Gen.stack in
  let bool_vars = new Gen.stack in
  let (pr_w,pr_s) = memo_complex_ops stk bool_vars is_complex in
  let f = drop_formula pr_w pr_s f in
  let ans = stk # get_stk in
  (f,ans, bool_vars # get_stk)

let memoise_rel_formula ivs (f:formula) : 
  (formula * ((Var.t * formula) list) * (Var.t list)) =
  let pr b = match b with
    | RelForm (i,_,p) -> false (* mem i ivs *)
    | _ ->
      (* Template: For soundness, do not remove 
       * templates which contains bound variables *)
      (* let bf = (b, None) in *)
      (* if has_template_b_formula bf then  *)
      (*   Gen.BList.subset_eq eq_spec_var  *)
      (*     (List.filter (fun v -> not (is_FuncT (type_of_spec_var v))) (bfv bf))  *)
      (*     (fv f) *)
      (* else *) false
  in memoise_formula_ho pr f

let memoise_rel_formula ivs (f:formula) : 
  (formula * ((Var.t * formula) list) * (Var.t list)) =
  let pr = string_of in
  let pr2 = pr_triple pr (pr_list (pr_pair Var.string_of pr)) Var.string_of_list in
  Debug.no_2 "memoise_rel_formula" Var.string_of_list pr pr2
      (fun _ _ -> memoise_rel_formula ivs f) ivs f

let has_template_formula f = false



let rec mkExists (vs : Var.t list) (f : formula) pos = match f with
    | Or (f1,f2) ->
          Or (mkExists vs f1 pos, mkExists vs f2 pos)
    | _ ->
        (* Pushing each ex v to the innermost location *)
    let fvs = fv f in
    let vs = List.filter (fun v -> Var.mem v fvs) vs in
    let fl = split_conjunctions f in
    let f_with_fv = List.map (fun f -> (fv f, f)) fl in
    let push_v v f_with_fv =
      let rel_f, nonrel_f = List.partition (fun (fvs, f) -> Var.mem v fvs) f_with_fv in
      let rel_fvs, rel_f = List.split rel_f in
      ((Gen.BList.difference_eq Var.equal (List.concat rel_fvs) [v]),
       (Exists (v, join_conjunctions rel_f pos)))::nonrel_f
    in
    join_conjunctions (snd (List.split
        ((List.fold_left (fun a v -> push_v v a) f_with_fv vs)))) pos

let rec mkForall (vs : Var.t list) (f : t) pos = match vs with
  | [] -> f
  | v :: rest ->
        let ef = mkForall rest f pos in
        if mem v (fv ef) then
          Forall (v, ef)
        else
          ef

let get_const_var p =
  match p with
    | BForm t -> Term.get_const_var t
    | _ -> []
(* a+a    --> 2*a
   1+3    --> 4
   1+x>-2 --> 3+x>0
*)
let rec arith_simplify_x (pf : t) : t =
  let rec helper pf = match pf with
      |  BForm b -> BForm (Term.arith_simplify b)
      |  And (f1, f2) -> And (helper f1, helper f2)
      |  Or (f1, f2) -> Or (helper f1, helper f2)
      |  Not f1 ->  Not (helper f1)
      |  Forall (v, f1) ->  Forall (v, helper f1)
      |  Exists (v, f1) ->  Exists (v, helper f1)
    in helper pf

and arith_simplify (pf : t) : t =
  Debug.no_1 ("arith_simplify") string_of string_of
    arith_simplify_x pf



(*
  decompose p0 into pointer equalities and arith
*)
let type_decomp p0=
  let aux_classify p=
    (* let svs = fv p in *)
    (* if List.for_all (fun sv -> is_node_typ sv.Var.t) svs then *)
    (*   p, mkTrue no_pos *)
    (* else if List.for_all (fun sv -> sv.Var.t == Int) svs then *)
    (*   mkTrue no_pos, p *)
    (* else *) Gen.report_error no_pos "Cpure.type_decomp: no separation on pointer and arith"
  in
  let rec helper p=
    match p with
      | BForm t-> let eqNulls, neqNulls, eqs, diseqs, r = Term.type_decomp t in
        (eqNulls, neqNulls, eqs, diseqs, BForm r)
      | Not _ -> ([], [], [], [], p) (* aux_classify p *)
      | Exists _ -> let qvars, p1 = split_quantifiers p in
        let eqNulls, neqNulls, eqs, diseqs, r = helper p1 in
        (eqNulls, neqNulls, eqs, diseqs, add_quantifiers qvars r)
      | Forall _ -> aux_classify p
      | And (f1, f2) ->
            let eqNulls1, neqNulls1, eq1, diseqs1, ar1 = helper f1 in
            let eqNulls2, neqNulls2, eq2, diseqs2, ar2 = helper f2 in
            eqNulls1@eqNulls2, neqNulls1@neqNulls2,eq1@eq2, diseqs1@diseqs2,  mkAnd ar1 ar2 no_pos
      | Or _ -> (* aux_classify p*)
            ([], [], [], [], p)
  in helper p0

let rec eql_simplify_x (pf0 : t) : t =
  let rec find_one_qvar qvars eqs=
    match eqs with
      | (v1, v2)::rest -> if Var.mem v1 qvars then
          (v1, v2)
        else if Var.mem v2 qvars then
          (v2, v1)
        else find_one_qvar qvars rest
      | [] -> raise Not_found
  in
  let rec fix_qvars_elim qvars pf=
    let _, _, eqs, _, _ = type_decomp pf in
    try
      let (v1, v2) = find_one_qvar qvars eqs in
      let n_pf = subst_var [(v1, v2)] pf in
      fix_qvars_elim (Var.diff qvars [v1]) n_pf
    with Not_found -> (qvars, pf)
  in
  let qvars, pf1 = split_quantifiers pf0 in
  let () = Debug.info_hprint (add_str  "qvars" (Var.string_of_list)) qvars no_pos in
  let r_qvars, r_pf = fix_qvars_elim qvars pf1 in
  if r_qvars == [] then r_pf
  else add_quantifiers r_qvars r_pf

and eql_simplify (pf : t) : t =
  Debug.no_1 ("eql_simplify") string_of string_of
    eql_simplify_x pf

let subtract_useless_diseq p vs=
  let ps = split_conjunctions p in
  let ps1 = List.filter (fun p -> begin
    match p with
      | BForm (Term.Neq (e1, e2, _)) -> begin
          match e1, e2 with
            | Exp.Var (v1, _), Exp.Var (v2, _) ->
                   ( (Var.mem v1 vs) && (Var.mem v2 vs))
            | _ -> true
        end
      | _ -> true
  end
  ) ps in
  join_conjunctions ps1 no_pos


let is_local_constraint p=
  match p with
    | BForm t -> Term.is_local_constraint t
    | _ -> false, false, false

let contain_const p=
  (* let ps = split_conjunctions p in *)
  (* List.for_all (fun p1 -> let _, _, is_local = is_local_constraint p1 in *)
  (* is_local *)
  (* ) ps *)
  false

let contain_rel p0=
  let rec aux p=
      match p with
        | BForm t -> Term.is_rel t
        | Not f
        | Exists (_, f) | Forall (_, f) -> aux f
        | And (f1, f2) | Or (f1, f2) ->
              (aux f1) || (aux f2)
  in
  aux p0

let is_rel p0=
  let rec aux p=
      match p with
        | BForm t -> Term.is_rel t
        | Not f
        | Exists (_, f) | Forall (_, f) -> aux f
        | And (f1, f2) | Or (f1, f2) ->
              false
  in
  aux p0

let rec decompose_rel p1 = match p1 with
  | BForm t -> Term.decompose_rel t
  | Not f | Exists (_, f) | Forall (_, f) -> decompose_rel f
  | _ -> raise Not_found


let subst_rel_x (b, h) p0=
  try
    let r_name, r_args = decompose_rel h in
    let ps = split_conjunctions p0 in
    let subst_ps = List.fold_left (fun r p -> begin
      try
        let r1_name, r1_args = decompose_rel p in
        if Ustr.str_eq r1_name r_name then
          let sst = List.combine r1_args r_args in
          let p1 = subst_var sst b in
          r@[p1]
        else r@[p]
      with _ -> r@[p]
    end
    ) ([]) ps in
    join_conjunctions subst_ps no_pos
  with _ -> p0

let subst_rel (b, h) p0=
  let pr1 = string_of in
  let pr2 = pr_pair pr1 pr1 in
  Debug.no_2 "subst_rel" pr2 pr1 pr1
      (fun _ _ ->  subst_rel_x (b, h) p0)
      (b, h) p0
