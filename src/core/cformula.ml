
open Globals
open Gen.Basic
open VarGen
open Gen

module CB = Csymheap
module CH = Cheap
module CP = Cpure

type formula =
  | Base of CB.formula
  | Exists of (CB.formula * (Var.t list))
  | Or of (formula * formula * loc)


and t = formula

let string_of cof0 =
  let rec helper cof =match cof with
    | Base f -> CB.string_of f
    | Exists (f, qvars) ->"(exists " ^ ((pr_list_no_brk Var.string_of) qvars) ^ ": "
            ^ (CB.string_of f) ^ ")"
    | Or (cof1, cof2, _) -> (helper cof1)^ " \n  or " ^ (helper cof2)
  in helper cof0

let mkTrue p = Base (CB.mkTrue p)

let mkFalse p = Base (CB.mkFalse p)

let isFalse f = match f with
  | Base fb -> CB.isFalse  fb
  | _ -> false

let mkBase h p l = Base (CB.mk h p l)

let mkExists quans h p pos =
   match h with
  | Cheap.HFalse -> mkFalse pos
  | _ ->
        if CP.isFalse p then mkFalse pos
        else
          if quans ==[] then Base (CB.mk h p pos)
          else Exists (CB.mk h p pos, quans)

let mkOr f1 f2 l = Or (f1, f2, l)

let isEmptyHeap f0=
  let rec aux f = match f with
    | Base f1
    | Exists (f1, _)  -> f1.CB.base_heap == Cheap.HEmp
    | Or (f1, f2, _) -> (aux f1) && (aux f2)
  in aux f0

let is_empty_true f0=
  let rec aux f = match f with
    | Base f1
    | Exists (f1, _)  -> f1.CB.base_heap == Cheap.HEmp &&
          CP.isTrue f1.CB.base_pure
    | Or (f1, f2, _) -> (aux f1) && (aux f2)
  in aux f0

let isHTrueHeap f0=
  let rec aux f = match f with
    | Base f1
    | Exists (f1, _)  -> f1.CB.base_heap == Cheap.HTrue
    | Or (f1, f2, _) -> (aux f1) && (aux f2)
  in aux f0

let is_pure_top f0=
  let rec aux f=
    match f with
      | Base fb
      | Exists (fb, _) -> if fb.CB.base_heap == Cheap.HTrue ||
          fb.CB.base_heap == Cheap.HEmp then
            let p1 = CP.remove_redundant fb.CB.base_pure in
            CP.isTrue p1
        else false
      | Or (f1, f2, _) -> (aux f1) && (aux f2)
  in aux f0

let rec add_quantifiers (qvars : Var.t list) (f : t) : t =
  if qvars == [] then f else
    match f with
      | Base f -> mkExists qvars f.CB.base_heap f.CB.base_pure f.CB.base_pos
      | Exists (f, qvs)  ->
            let new_qvars = Var.remove_dups (qvs @ qvars) in
            mkExists new_qvars f.CB.base_heap f.CB.base_pure f.CB.base_pos
      | Or (f1, f2, pos) -> Or (add_quantifiers qvars f1, add_quantifiers qvars f2, pos)

let split_quantifiers (f : t) : (Var.t list * t) =
  match f with
    | Exists (b, qvars) -> (qvars, Base b)
    | Base _ -> ([], f)
    | _ -> failwith ("split_quantifiers: invalid argument (formula_or)")

let fresh_quantifiers (f0 : t) : ( t) =
  let rec aux f= match f with
    | Exists (b, qvars) ->
          let n_qvars = Var.fresh_vars qvars in
          let sst = List.combine qvars n_qvars in
          Exists (CB.subst sst b, n_qvars)
    | Base _ -> f
    | Or (f1, f2, pos) -> Or (aux f1, aux f2, pos)
  in aux f0

let simplify_pure (f0 : t) : ( t) =
  let rec aux f= match f with
    | Exists (b, qvars) ->
          Exists ({b with  CB.base_pure = CP.remove_redundant b.CB.base_pure},
          qvars)
    | Base b -> Base {b with CB.base_pure = CP.remove_redundant b.CB.base_pure}
    | Or (f1, f2, pos) -> Or (aux f1, aux f2, pos)
  in aux f0

let rec push_exists (qvars : Var.t list) (f : t)=
  match f with
    | Or (f1, f2,  pos) ->
          let new_f1 = push_exists qvars f1 in
          let new_f2 = push_exists qvars f2 in
          let resform = mkOr new_f1 new_f2 pos in
          resform
    | _ -> add_quantifiers qvars f

let subst_x sst (f0 : t) =
  let rec helper f = match f with
    | Or ( f1, f2, pos) ->
          Or (helper f1, helper f2, pos)
    | Base b -> Base (CB.subst sst b)
    | Exists (b, qsv) ->
          (* Variable under this existential quantification should NOT be substituted! *)
          (* Thus, we need to filter out replacements (fr |-> t) in sst where fr is in qsv *)
          let qsvnames = (List.map Var.name_of qsv) in
          let sst = List.filter (fun (fr,_) -> not (List.mem (Var.name_of fr) qsvnames)) sst in
          if sst = [] then f else
            Exists (CB.subst sst b, qsv)
  in
  helper f0

let subst sst (f : t) =
  let pr1 = pr_list (pr_pair Var.string_of Var.string_of) in
  let pr2 = string_of in
  Debug.no_2 "subst" pr1 pr2 pr2 subst_x sst f

let subst_type t_sst (f0 : t) =
  let rec helper f = match f with
    | Or ( f1, f2, pos) ->
          Or (helper f1, helper f2, pos)
    | Base b -> Base (CB.subst_type t_sst b)
    | Exists (b, qsv) ->
          let qsvnames = (List.map (Var.subst_type t_sst) qsv) in
          Exists (CB.subst_type t_sst b, qsvnames)
  in if t_sst ==[] then f0 else helper f0

let subst_view_inv_x pred_invs f0=
  (*****************************************)
  let rec subst_helper f= match f with
    | Base fb -> Base (CB.subst_view_inv pred_invs fb)
    | Exists _ ->
          let quans,bare = split_quantifiers f in
          let nf = subst_helper  bare in
          (add_quantifiers quans nf)
    | Or (f1, f2, pos) -> Or (subst_helper f1, subst_helper f2, pos)
  in
  (*****************************************)
  if pred_invs = [] then f0 else subst_helper f0

let subst_view_inv pred_invs f=
  let pr1= string_of in
  let pr2 = pr_pair pr_id (pr_pair Var.string_of_list CP.string_of) in
  Debug.no_2 "subst_view_inv" (pr_list_ln pr2) pr1 pr1
      (fun _ _ -> subst_view_inv_x pred_invs f)
      pred_invs f

let fv (f0 : t) : Var.t list=
  let rec helper f= match f with
    | Or (f1, f2, _) ->
          Var.remove_dups (helper f1 @ helper f2)
    | Base b -> CB.fv b
    | Exists (b, qvars) ->
          let fvars =  CB.fv b in
          let qvars = Var.remove_dups qvars in
          let res = Var.diff fvars qvars in
          res
  in helper f0

let rec list_of_disjuncts f= match f with
  | Or (f1, f2, _) -> (list_of_disjuncts f1)@(list_of_disjuncts f2)
  | _ -> [f]

let to_disjunct_form fs=
  match fs with
    | f::rest -> List.fold_left (fun acc_f f1 -> Or (acc_f, f1, no_pos)) f rest
    | [] -> failwith "Cformula.to_disjunct_form: not allowed empty list"

let sequentialize_views_x f0=
  let rec helper f=
    match f with
      | Base fb -> Base (CB.sequentialize_views fb)
      | Exists (fb, qvars) -> Exists (CB.sequentialize_views fb, qvars)
      | Or (f1, f2, pos) -> Or (helper f1, helper f2, pos)
  in helper f0

let sequentialize_views f0=
  Debug.no_1 "sequentialize_views" string_of string_of
      (fun _ -> sequentialize_views_x f0) f0

let mkStarAnd ?avoid_clash:(ac=true) f1 f2=
  let mkStarAnd_aux is_ac f01 f02=
    match f01, f02 with
      | Base fb1, Base fb2 -> Base (CB.mkStarAnd fb1 fb2)
      | Base fb1, Exists (fb2, qvars)
      | Exists (fb1, qvars), Base fb2 -> Exists (CB.mkStarAnd fb1 fb2, qvars)
      | Exists (fb1, qvars1), Exists (fb2, qvars2) ->
            let qvars, n_fb2 = if is_ac then
              let inter_vars = Var.intersect qvars2 qvars1 in
              if inter_vars==[] then (qvars1@qvars2, fb2)
              else
                let fr_vars = Var.fresh_vars inter_vars in
                let sst = List.combine inter_vars fr_vars in
                let n_qvars2 = List.map (Var.subst sst) qvars2 in
                let n_fb2 = CB.subst sst fb2 in
                (qvars1@n_qvars2, n_fb2)
            else (Var.remove_dups (qvars2@qvars2), fb2) in
            Exists (CB.mkStarAnd fb1 n_fb2, qvars)
      | _ -> failwith "Cformula.mkStarAnd: disj can not happen"
  in
  let disj1 = list_of_disjuncts f1 in
  let disj2 = list_of_disjuncts f2 in
  let comb_disj = List.fold_left (fun fs f10 ->
      let fs2 = List.map (mkStarAnd_aux ac f10) disj2 in
      fs@[to_disjunct_form fs2]
  ) [] disj1 in
  to_disjunct_form comb_disj

let mkPureAnd f p=
  let f2 = mkBase CH.HEmp p no_pos in
  mkStarAnd f f2

let contain_pred f0 pred_name=
  let rec aux f= match f with
    | Base fb
    | Exists (fb, _) -> CH.contain_pred fb.CB.base_heap pred_name
    | Or (f1, f2, _ ) -> (aux f1) || (aux f2)
  in aux f0

let subtract_pto f0 pto=
  let rec aux f= match f with
    | Base fb -> Base (CB.subtract_pto fb pto)
    | Exists (fb, qvars) -> let fb1 = aux (Base fb) in
      add_quantifiers qvars fb1
    | Or (f1, f2, pos) -> Or (aux f1, aux f2, pos)
  in aux f0

let subtract_pred f0 vn=
  let rec aux f= match f with
    | Base fb -> Base (CB.subtract_pred fb vn)
    | Exists (fb, qvars) -> let fb1 = aux (Base fb) in
      add_quantifiers qvars fb1
    | Or (f1, f2, pos) -> Or (aux f1, aux f2, pos)
  in aux f0

let subtract_useless_diseq f0 vs=
  let rec aux f= match f with
    | Base fb -> Base {fb with CB.base_pure = CP.subtract_useless_diseq fb.CB.base_pure vs}
    | Exists (fb, qvars) -> let fb1 = aux (Base fb) in
      add_quantifiers qvars fb1
    | Or (f1, f2, pos) -> Or (aux f1, aux f2, pos)
  in aux f0

let star_decompose f0=
  let rec aux f= match f with
    | Base fb -> CH.star_decompose fb.CB.base_heap
    | Exists (fb, qvars) -> CH.star_decompose fb.CB.base_heap
    | Or (f1, f2, _) ->
          let ps1, vs1 = aux f1 in
          let ps2, vs2 = aux f2 in
          (ps1@ps2, vs1@vs2)
  in aux f0

let decompose f0=
  let rec aux f= match f with
    | Base fb -> let vns, ptos = CH.star_decompose fb.CB.base_heap in
      ([], vns, ptos, fb.CB.base_pure)
    | Exists (fb, qvars) -> let vns, ptos = CH.star_decompose fb.CB.base_heap in
      (qvars, vns, ptos, fb.CB.base_pure)
    | Or _ -> failwith "Cformula.decompose: not for disjunction"
  in aux f0

let update_view_unfold_number num f0=
  let rec aux f= match f with
      | Base fb -> Base {fb with CB.base_heap = CH.update_view_unfold_number num fb.CB.base_heap}
      | Exists (fb, qvars) -> let nfb = {fb with CB.base_heap = CH.update_view_unfold_number num fb.CB.base_heap} in
            Exists (nfb, qvars)
      | Or (f1, f2, pos) -> Or (aux f1, aux f2, pos)
  in aux f0


let increase_view_unfold_number f0=
  let rec aux f= match f with
      | Base fb -> Base {fb with CB.base_heap = CH.increase_view_unfold_number fb.CB.base_heap}
      | Exists (fb, qvars) -> let nfb = {fb with CB.base_heap = CH.increase_view_unfold_number fb.CB.base_heap} in
            Exists (nfb, qvars)
      | Or (f1, f2, pos) -> Or (aux f1, aux f2, pos)
  in aux f0


let equal_x f1 f2=
  match f1,f2 with
    | Base fb1, Base fb2 -> CB.equal fb1 fb2
    | Exists (fb1, qvars1), Exists (fb2, qvars2) -> begin
        try
          let sst = List.combine (Var.diff qvars2 qvars1)
            (Var.diff qvars1 qvars2) in
          CB.equal fb1 (CB.subst sst fb2)
        with _ -> false
      end
    | _ -> false

let equal f1 f2=
  let pr1 = string_of in
  Debug.no_2 "equal" pr1 pr1 string_of_bool
      (fun _ _ -> equal_x f1 f2) f1 f2

let remove_redundant_x f0=
  let aux_pure p=
    let nullVars, neqNullVars, _, _, _ = CP.type_decomp p in
    if List.exists (fun v1 -> List.exists (fun v2 -> Var.equal v1 v2) neqNullVars) nullVars then
      true, CP.mkFalse no_pos
    else
      false, CP.remove_redundant p
  in
  let rec aux f=
    match f with
      | Base fb -> let is_unsat,  np = aux_pure fb.CB.base_pure in
        let nf = Base {fb with CB.base_pure = np} in
        is_unsat, nf
      | Exists (fb, qvars) ->
            let is_unsat,  np = aux_pure fb.CB.base_pure in
            let nf = Exists ({fb with CB.base_pure = np}, qvars) in
            is_unsat, nf
      | Or (f1, f2, pos) ->
            let r1, f11 = aux f1 in
            if r1 then aux f2
            else
              let r2, f22 = aux f2 in
              if r2 then r1, f11
              else (false, Or (f11, f22, pos))
  in aux f0

let remove_redundant f0=
  Debug.no_1 "Cformula.remove_redundant"
      string_of (pr_pair string_of_bool string_of)
      (fun _ -> remove_redundant_x f0) f0

let remove_dups_x f0=
  let fs = list_of_disjuncts f0 in
  let fs1 = BList.remove_dups_eq equal fs in
  to_disjunct_form fs1

let remove_dups f0=
  Debug.no_1 "Cformula.remove_dups" string_of string_of
      (fun _ -> remove_dups_x f0) f0
