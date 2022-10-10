open Globals
open VarGen
open Gen.Basic
open Gen

open Exp
open Var


type term =
  | BConst of (bool * loc)
  | BVar of (Var.t * loc)
  | Lt of (Exp.t * Exp.t * loc)
  | Lte of (Exp.t * Exp.t * loc)
  | Gt of (Exp.t * Exp.t * loc)
  | Gte of (Exp.t * Exp.t * loc)
  | Eq of (Exp.t * Exp.t * loc) (* these two could be arithmetic or pointer or bag or list *)
  | Neq of (Exp.t * Exp.t * loc)
  | EqMax of (Exp.t * Exp.t * Exp.t * loc) (* first is max of second and third *)
  | EqMin of (Exp.t * Exp.t * Exp.t * loc) (* first is min of second and third *)
  (* bag formulas *)
  | BagIn of (Var.t * Exp.t * loc)
  | BagNotIn of (Var.t * Exp.t * loc)
  | BagSub of (Exp.t * Exp.t * loc)
  | BagMin of (Var.t * Var.t * loc)
  | BagMax of (Var.t * Var.t * loc)
  (*string logic*)
  | RelForm of (ident * (Exp.t list) * loc)

type t = term


let rec string_of t=
  match t with
    | BConst (b, p) -> string_of_bool b
    | BVar (sv, p) -> Var.string_of sv
    | Lt (e1, e2, p) -> (Exp.string_of e1) ^ "<" ^ (Exp.string_of e2)
    | Lte (e1, e2, p) -> (Exp.string_of e1) ^ "<=" ^ (Exp.string_of e2)
    | Gt (e1, e2, p) -> (Exp.string_of e1) ^ ">" ^ (Exp.string_of e2)
    | Gte (e1, e2, p) -> (Exp.string_of e1) ^ ">=" ^ (Exp.string_of e2)
    | Eq (e1, e2, p) -> (Exp.string_of e1) ^ "=" ^ (Exp.string_of e2)
    | Neq (e1, e2, p) -> (Exp.string_of e1) ^ "!=" ^ (Exp.string_of e2)
    | EqMax (e1, e2, e3, p) -> "EqMax"
    | EqMin (e1, e2, e3, p) -> "EqMin"
          (* bag formulas *)
    | BagIn (sv, e, p) -> "BagIn"
    | BagNotIn (sv, e, p) -> "BagNotIn"
    | BagSub (e1, e2, p) -> "BagSub"
    | BagMin (e1, e2, p) -> "BagMin"
    | BagMax (e1, e2, p) -> "BagMax"
          (*string logic*)
    | RelForm (id, exps, _) -> ((* Var.string_of *) id)^"("^((pr_list Exp.string_of) exps)^")"


let is_string_term t= match t with
  | Eq (e1, e2, _)
  | Neq (e1, e2, _) -> (Exp.is_string_exp e1) && (Exp.is_string_exp e2)
  | _ -> false

let is_arith_term t= match t with
  | Lt (e1, e2, _)
  | Lte (e1, e2, _)
  | Gt (e1, e2, _)
  | Gte (e1, e2, _)
  | Eq (e1, e2, _)
  | Neq (e1, e2, _) -> (Exp.is_arith_exp e1) && (Exp.is_arith_exp e2)
  | _ -> false

let is_simple_word_equation t= match t with
  | Eq (e1, e2, _)
  | Neq (e1, e2, _) -> (Exp.is_string_var e1) || (Exp.is_string_var e2) ||
        (Exp.is_string_const e1 && Exp.is_string_const e2)
  | _ -> false



let is_update_array_relation (r:string) = 
  let udrel = "update_array" in
  let udl = String.length udrel in
  (String.length r) >= udl && (String.sub r 0 udl) = udrel

let fv pf = match pf with
  | BConst _ -> []
  | BVar (bv, _) -> [bv]
  | Lt (a1, a2, _) 
  | Lte (a1, a2, _) 
  | Gt (a1, a2, _) 
  | Gte (a1, a2, _) 
  | Eq (a1, a2, _) 
  | Neq (a1, a2, _) -> combine_avars a1 a2
  | EqMax (a1, a2, a3, _) ->
    let fv1 = Exp.fv a1 in
    let fv2 = Exp.fv a2 in
    let fv3 = Exp.fv a3 in
    remove_dups (fv1 @ fv2 @ fv3)
  | EqMin (a1, a2, a3, _) ->
    let fv1 = Exp.fv a1 in
    let fv2 = Exp.fv a2 in
    let fv3 = Exp.fv a3 in
    remove_dups (fv1 @ fv2 @ fv3)
  | BagIn (v, a1, _) ->
    let fv1 = Exp.fv a1 in
    [v] @ fv1
  | BagNotIn (v, a1, _) ->
    let fv1 = Exp.fv a1 in
    [v] @ fv1
  | BagSub (a1, a2, _) -> Exp.combine_avars a1 a2
  | BagMax (v1, v2, _) -> remove_dups ([v1] @ [v2])
  | BagMin (v1, v2, _) -> remove_dups ([v1] @ [v2])
  | RelForm (r, args, _) ->
    (* let vid = r in *)
    (* vid:: *)remove_dups (List.fold_left List.append [] (List.map Exp.fv args))


let mkEq e1 e2 pos= (Eq (e1, e2, pos))

let mkNeq e1 e2 pos= (Neq (e1, e2, pos))

let mkGt e1 e2 pos= (Gt (e1, e2, pos))

let mkGte e1 e2 pos= (Gte (e1, e2, pos))

let mkLt e1 e2 pos= (Lt (e1, e2, pos))

let mkLte e1 e2 pos= (Lte (e1, e2, pos))

let mkTrue pos = BConst (true, pos)

let mkFalse pos = BConst (false, pos)

let mkEqN e n pos = (Eq (e, Exp.mkN n no_pos, pos))

let mkEqZero e pos = mkEqN e 0 pos

let mkGtZero e pos = (Gt (e, Exp.mkZero no_pos, pos))

let mkGteZero e pos = (Gte (e, Exp.mkZero no_pos, pos))

let mkRel id args pos = RelForm (id, List.map (fun v -> Exp.mkVar v pos) args, pos)

let equalTerm (eq:Var.t -> Var.t -> bool) (pf1:t)(pf2:t):bool =
  match (pf1,pf2) with
  | (BConst(c1, _), BConst(c2, _)) -> c1 = c2
  | (BVar(sv1, _), BVar(sv2, _)) -> (eq sv1 sv2)
  | (Lte(IConst(i1, _), e2, _), Lt(IConst(i3, _), e4, _)) -> i1=i3+1 && Exp.eqExp_f eq e2 e4
  | (Lte(e1, IConst(i2, _), _), Lt(e3, IConst(i4, _), _)) -> i2=i4-1 && Exp.eqExp_f eq e1 e3
  | (Lt(IConst(i1, _), e2, _), Lte(IConst(i3, _), e4, _)) -> i1=i3-1 && Exp.eqExp_f eq e2 e4
  | (Lt(e1, IConst(i2, _), _), Lte(e3, IConst(i4, _), _)) -> i2=i4+1 && Exp.eqExp_f eq e1 e3
  | (Gte(IConst(i1, _), e2, _), Gt(IConst(i3, _), e4, _)) -> i1=i3-1 && Exp.eqExp_f eq e2 e4
  | (Gte(e1, IConst(i2, _), _), Gt(e3, IConst(i4, _), _)) -> i2=i4+1 && Exp.eqExp_f eq e1 e3
  | (Gt(IConst(i1, _), e2, _), Gte(IConst(i3, _), e4, _)) -> i1=i3+1 && Exp.eqExp_f eq e2 e4
  | (Gt(e1, IConst(i2, _), _), Gte(e3, IConst(i4, _), _)) -> i2=i4-1 && Exp.eqExp_f eq e1 e3
  (* | (Lte(e1, e2, _), Gt(e4, e3, _)) *)
  | (Lte(e1, e2, _), Gte(e4, e3, _))
  | (Gte(e1, e2, _), Lte(e4, e3, _))
  (* | (Gt(e1, e2, _), Lte(e4, e3, _)) *)
  | (Gte(e1, e2, _), Lt(e4, e3, _))
  (* | (Lt(e1, e2, _), Gte(e4, e3, _)) *) (* unsound *)
  | (Lte(e1, e2, _), Lte(e3, e4, _))
  | (Gt(e1, e2, _), Gt(e3, e4, _))
  | (Gte(e1, e2, _), Gte(e3, e4, _))
  | (Lt(e1, e2, _), Lt(e3, e4, _)) -> (Exp.eqExp_f eq e1 e3) && (Exp.eqExp_f eq e2 e4)
  | (Neq(e1, e2, _), Neq(e3, e4, _))
  | (Eq(e1, e2, _), Eq(e3, e4, _)) -> ((Exp.eqExp_f eq e1 e3) && (Exp.eqExp_f eq e2 e4)) || ((Exp.eqExp_f eq e1 e4) && (Exp.eqExp_f eq e2 e3))
  | (EqMax(e1, e2, e3, _), EqMax(e4, e5, e6, _))
  | (EqMin(e1, e2, e3, _), EqMin(e4, e5, e6, _))  -> (Exp.eqExp_f eq e1 e4) && ((Exp.eqExp_f eq e2 e5) && (Exp.eqExp_f eq e3 e6)) || ((Exp.eqExp_f eq e2 e6) && (Exp.eqExp_f eq e3 e5))
  | (BagIn(sv1, e1, _), BagIn(sv2, e2, _))
  | (BagNotIn(sv1, e1, _), BagNotIn(sv2, e2, _)) -> (eq sv1 sv2) && (Exp.eqExp_f eq e1 e2)
  | (BagMin(sv1, sv2, _), BagMin(sv3, sv4, _))
  | (BagMax(sv1, sv2, _), BagMax(sv3, sv4, _)) -> (eq sv1 sv3) && (eq sv2 sv4)
  | (BagSub(e1, e2, _), BagSub(e3, e4, _)) -> (Exp.eqExp_f eq e1 e3) && (Exp.eqExp_f eq e2 e4)
  | (RelForm (r1,args1,_), RelForm (r2,args2,_)) -> (* (equal r1 r2) *)
        Ustr.str_eq r1 r2
        && (Exp.eqExp_list_f eq args1 args2)
  | _ -> false

let rec t_subst_one_term ((fr, t) : (Var.t * Exp.t)) pf =
  let npf = let rec helper pf =
    match pf with
      | BConst _ -> pf
      | BVar (bv, pos) ->
            if equal bv fr then
              match t with 
                | Var (t,_) -> BVar (t,pos)
                | _ -> failwith ("Presburger.b_apply_one_term: attempting to substitute arithmetic term for boolean var")
            else
              pf
      | Lt (a1, a2, pos) -> Lt (Exp.subst_one_term (fr, t) a1, Exp.subst_one_term (fr, t) a2, pos)
      | Lte (a1, a2, pos) -> Lte (Exp.subst_one_term (fr, t) a1, Exp.subst_one_term (fr, t) a2, pos)
      | Gt (a1, a2, pos) -> Gt (Exp.subst_one_term (fr, t) a1, Exp.subst_one_term (fr, t) a2, pos)
      | Gte (a1, a2, pos) -> Gte (Exp.subst_one_term (fr, t) a1, Exp.subst_one_term (fr, t) a2, pos)
      | Eq (a1, a2, pos) -> Eq (Exp.subst_one_term (fr, t) a1,Exp.subst_one_term (fr, t) a2, pos)
      | Neq (a1, a2, pos) -> Neq (Exp.subst_one_term (fr, t) a1, Exp.subst_one_term (fr, t) a2, pos)
      | EqMax (a1, a2, a3, pos) -> EqMax (Exp.subst_one_term (fr, t) a1, Exp.subst_one_term (fr, t) a2, Exp.subst_one_term (fr, t) a3, pos)
      | EqMin (a1, a2, a3, pos) -> EqMin (Exp.subst_one_term (fr, t) a1, Exp.subst_one_term (fr, t) a2, Exp.subst_one_term (fr, t) a3, pos)
      | BagIn (v, a1, pos) -> 
            let new_v = if equal v fr then
              match t with
                | Var (tv,pos) -> tv
                | _ ->
                      let () = print_endline_quiet "[Warning] b_apply_one_term: cannot replace a bag variable with an expression" in
                      v
            else v
            in
            BagIn (new_v, Exp.subst_one_term (fr, t) a1, pos)(*what if v is a variable that need to be applied ??? MAY need to expect v to expression as well*)
      | BagNotIn (v, a1, pos) ->
            let new_v = if equal v fr then
              match t with
                | Var (tv,pos) -> tv
                | _ ->
                      let () = print_endline_quiet "[Warning] b_apply_one_term: cannot replace a bag variable with an expression" in
                      v
            else v
            in
            BagNotIn (new_v, Exp.subst_one_term (fr, t) a1, pos)
      | BagSub (a1, a2, pos) -> BagSub (Exp.subst_one_term (fr, t) a1, Exp.subst_one_term (fr, t) a2, pos)
      | BagMax (v1, v2, pos) -> BagMax (v1, v2, pos)
      | BagMin (v1, v2, pos) -> BagMin (v1, v2, pos)
      | RelForm (r, args, pos) -> RelForm (r, List.map (Exp.subst_one_term (fr, t)) args, pos)
  in helper pf
  in match npf with
    | Eq (Exp.Var (v1, _ ), Exp.Var (v2, _ ), pos) -> if Var.equal v1 v2 then
        BConst (true, pos)
      else npf
    | _ -> npf

let t_subst sst t=
  List.fold_left (fun t0 ss -> t_subst_one_term ss t0) t sst

let subst sst t=
  let e_sst = List.map (fun (sv1, sv2) ->
      (sv1, Exp.Var (sv2, no_pos))
  ) sst in
  t_subst e_sst t

let rec subst_type t_sst pf0 =
  let rec helper pf = match pf with
      | BConst _ -> pf
      | BVar (bv, pos) -> BVar (Var.subst_type t_sst bv, pos)
      | Lt (a1, a2, pos) -> Lt (Exp.subst_type t_sst a1, Exp.subst_type t_sst a2, pos)
      | Lte (a1, a2, pos) -> Lte (Exp.subst_type t_sst a1, Exp.subst_type t_sst a2, pos)
      | Gt (a1, a2, pos) -> Gt (Exp.subst_type t_sst a1, Exp.subst_type t_sst a2, pos)
      | Gte (a1, a2, pos) -> Gte (Exp.subst_type t_sst a1, Exp.subst_type t_sst a2, pos)
      | Eq (a1, a2, pos) -> Eq (Exp.subst_type t_sst a1, Exp.subst_type t_sst a2, pos)
      | Neq (a1, a2, pos) -> Neq (Exp.subst_type t_sst a1, Exp.subst_type t_sst a2, pos)
      | EqMax (a1, a2, a3, pos) -> EqMax (Exp.subst_type t_sst a1, Exp.subst_type t_sst a2, Exp.subst_type t_sst a3, pos)
      | EqMin (a1, a2, a3, pos) -> EqMin (Exp.subst_type t_sst a1, Exp.subst_type t_sst a2, Exp.subst_type t_sst a3, pos)
      | BagIn (v, a1, pos) -> 
            BagIn (Var.subst_type t_sst v, Exp.subst_type t_sst a1, pos)
      | BagNotIn (v, a1, pos) ->
            BagNotIn (Var.subst_type t_sst v, Exp.subst_type t_sst a1, pos)
      | BagSub (a1, a2, pos) -> BagSub (Exp.subst_type t_sst a1, Exp.subst_type t_sst a2, pos)
      | BagMax (v1, v2, pos) -> BagMax (Var.subst_type t_sst v1, Var.subst_type t_sst v2, pos)
      | BagMin (v1, v2, pos) -> BagMin (Var.subst_type t_sst v1, Var.subst_type t_sst v2, pos)
      | RelForm (r, args, pos) -> RelForm (r, List.map (Exp.subst_type t_sst) args, pos)
  in helper pf0

let is_ew_trivial_true_x t has_arith=
  match t with
    | Eq (t1, t2, _) -> begin
        (* t1 = t2 syntactically *)
        if Exp.eqExp_f Var.equal t1 t2 then true else
          if has_arith then false else
            (* either t1 or t2 is a variable *)
            let is_sl = match t1 with
              | Exp.Var _ -> true
              | _ -> begin
                  match t2 with
                    | Exp.Var _ -> true
                    | _ -> false
                end
            in
            is_sl
      end
    | _ -> false

let is_ew_trivial_true t has_arith=
  let pr1 = string_of in
  let pr2 = string_of_bool in
  Debug.no_1 "is_ew_trivial_true" pr1 pr2
      (fun _ -> is_ew_trivial_true_x t has_arith) t

let rec head_of_string_x t=
  match t with
    | Exp.CConst _ -> Some t
    | Exp.Var _ -> Some t
    | Exp.Concat (t1, _ ,_) -> head_of_string_x t1
    | _ -> None

let rec is_only_head t=
  match t with
    | Exp.CConst _
    | Exp.Var _ -> true
    | _ -> false

let head_of_string t=
  let pr1 = Exp.string_of in
  let pr2 = pr_option pr1 in
  Debug.no_1 "head_of_string" pr1 pr2
      (fun _ -> head_of_string_x t) t

let is_ew_trivial_false_x t=
   match t with
    | Eq (t1, t2, _) -> begin
        match head_of_string t1, head_of_string t2 with
          | Some t11, Some t12 -> begin
              match t11, t12 with
                | Exp.CConst (c1, _), Exp.CConst (c2, _) ->
                      not(c1==c2)
                | _ -> false
            end
          | _ -> false
      end
    | _ -> false


let is_ew_trivial_false t=
  let pr1 = string_of in
  let pr2 = string_of_bool in
  Debug.no_1 "is_ew_trivial_false" pr1 pr2
      (fun _ -> is_ew_trivial_false_x t) t


let normalize_word_eq t=
  match t with
    | Eq (e1, e2, p) -> Eq (Exp.normalize_concat e1, Exp.normalize_concat e2, p)
    | _ -> t


let string_to_length_x t=
  match t with
    | Eq (e1, e2, p) ->
          let n_e1 = Exp.string_to_length e1 in
          let n_e2 = Exp.string_to_length e2 in
          Eq (n_e1, n_e2, p)
    | _ -> raise (Invalid_argument "Term.string_to_length")

let string_to_length t=
  Debug.no_1 "Term.string_to_length" string_of string_of
      (fun _ -> string_to_length_x t) t

let get_cconst_x ew=
  match ew with
    | Eq (e1, e2, _) -> BList.remove_dups_eq (Exp.eqExp_f Var.equal) ((Exp.get_cconst e1)@(Exp.get_cconst e2))
    | _ -> []

let get_cconst ew=
  Debug.no_1 "Term.get_cconst" string_of (pr_list Exp.string_of)
      (fun _ -> get_cconst_x ew) ew

let get_const_var t =
  match t with
    | Eq (e1, e2, _) -> begin
        match e1 with
          | Exp.Var (sv, _) -> begin
              match e2 with
                | Exp.IConst _ | Exp.FConst _ | Exp.SConst _ | Exp.CConst _ | Exp.Null _ -> [sv]
                | _ -> []
            end
          | Exp.IConst _ | Exp.FConst _ | Exp.SConst _ | Exp.CConst _ | Exp.Null _ -> begin
              match e2 with
                | Exp.Var (sv, _) -> [sv]
                | _ -> []
            end
          | _ -> []
      end
    | _ -> []


and arith_simplify (pf: t) : t =
  let do_all e1 e2 l =
    let t1 = Exp.simp_mult e1 in
    let t2 = Exp.simp_mult e2 in
    let t1 = Exp.purge_mult t1 in
    let t2 = Exp.purge_mult t2 in
    let (lhs, lsm) = Exp.split_sums t1 in
    let (rhs, rsm) = Exp.split_sums t2 in
    let (lh, rh) = Exp.move_lr lhs lsm rhs rsm l in
    (* purge_mult will convert 1*x => x and 0*x => 0
       but this code seems inefficient *)
    let lh = Exp.purge_mult lh in
    let rh = Exp.purge_mult rh in
    (lh, rh) in
  let build_eq lhs rhs = 
    (* to simplify to v=rhs *)
    (lhs,rhs) in
  let do_all_eq e1 e2 l = 
    let r = do_all e1 e2 l in
    r
  in
  let do_all_eq e1 e2 l = 
    let pr = Exp.string_of in
      Debug.no_2 "do_all_eq" pr pr (pr_pair pr pr) (fun _ _ -> do_all_eq e1 e2 l) e1 e2
  in
  let do_all3 e1 e2 e3 l =
    let t1 = Exp.simp_mult e1 in
    let t2 = Exp.simp_mult e2 in
    let t3 = Exp.simp_mult e3 in
    let (lhs, lsm) = Exp.split_sums t1 in
    let (rhs, rsm) = Exp.split_sums t2 in
    let (qhs, qsm) = Exp.split_sums t3 in
    let ((lh,rh,qh),flag) =
      match (lhs,rhs,qhs,lsm,rsm,qsm) with
      (* -x = max(-y,-z) ==> x = min(y,z) *)
      | None,None,None,Some lh,Some rh, Some qh -> ((lh,rh,qh),false)
      | _,_,_,_,_,_ -> (move_lr3 lhs lsm rhs rsm qhs qsm l,true) in
    let lh = Exp.purge_mult lh in
    let rh = Exp.purge_mult rh in
    let qh = Exp.purge_mult qh in
    (lh, rh, qh,flag) in
  let do_all3_eq e1 e2 e3 l = 
    let pr = Exp.string_of in
      Debug.no_3 "do_all3_eq" pr pr pr (pr_quad pr pr pr string_of_bool) (fun _ _ _ -> do_all3 e1 e2 e3 l) e1 e2 e3
  in
  let rec helper pf =
    match pf with
      |  BConst _  |  BVar _ -> pf
      |  Lt (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
             Lt (lh, rh, l)
      |  Lte (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
             Lte (lh, rh, l)
      |  Gt (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
             Lt (rh, lh, l)
      |  Gte (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
             Lte (rh, lh, l)
      |  Eq (e1, e2, l) ->
             let lh, rh = do_all_eq e1 e2 l in
             Eq (lh, rh, l)
      |  Neq (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
             Neq (lh, rh, l)
      |  EqMax (e1, e2, e3, l) ->
             let lh,rh,qh,flag = do_all3_eq e1 e2 e3 l in
             if flag then EqMax (lh,rh,qh,l)
             else EqMin (lh,rh,qh,l)
      |  EqMin (e1, e2, e3, l) ->
             let lh,rh,qh,flag = do_all3_eq e1 e2 e3 l in
             if flag then EqMin (lh,rh,qh,l)
             else EqMax (lh,rh,qh,l)
      |  BagIn (v, e1, l) ->  BagIn (v, Exp.purge_mult (Exp.simp_mult e1), l)
      |  BagNotIn (v, e1, l) -> BagNotIn (v, Exp.purge_mult (Exp.simp_mult e1), l)
      |  BagSub (e1, e2, l) -> BagSub (Exp.simp_mult e1, Exp.simp_mult e2, l)
      |  BagMin _ -> pf
      |  BagMax _ -> pf
      |  RelForm (v,exs,p) ->
             let new_exs = List.map (fun e ->
                 Exp.purge_mult (Exp.simp_mult e)) exs
             in
             RelForm (v,new_exs,p)
  in helper pf


let type_decomp tp=
  match tp with
    | Eq (e1, e2, p) -> begin
        match e1,e2 with
          | Exp.Null _, Exp.Var (sv, _)
          | Exp.Var (sv, _), Exp.Null _ ->
                (* if is_node_typ sv.Var.t then *)
                  [sv],[],[],[], mkTrue p
                (* else ([],[],[],[], tp) *)
          | Exp.Var (sv1, _), Exp.Var (sv2, _) ->
                (* if Globals.is_node_typ sv1.Var.t && Globals.is_node_typ sv2.Var.t then *)
                  [],[],[(sv1,sv2)],[], mkTrue p
                (* else ([],[],[],[], tp) *)
          | _ -> [],[],[],[], tp
      end
    | Neq (e1, e2, p) -> begin
        match e1,e2 with
          | Exp.Null _, Exp.Var (sv, _)
          | Exp.Var (sv, _), Exp.Null _ ->
                (* if is_node_typ sv.Var.t then *)
                  [],[sv],[],[], mkTrue p
                (* else ([],[],[],[], tp) *)
          | Exp.Var (sv1, _), Exp.Var (sv2, _) ->
                (* if is_node_typ sv1.Var.t && is_node_typ sv2.Var.t then *)
                  [],[],[],[(sv1,sv2)], mkTrue p
                (* else ([],[],[],[], tp) *)
          | _ -> [],[],[],[], tp
      end
    | _ -> ([],[],[],[], tp)


let is_local_constraint t=
  match t with
    | Lt (Exp.Var _, e2, _) | Gt (e2, Exp.Var _, _)  -> begin
        match e2 with
          | Exp.Var _ -> true, true, true
          | Exp.Add (Exp.Var _, IConst (i, _), _)
          | Exp.Add ( IConst (i, _), Exp.Var _, _) ->
                 i<=0, i<=0, true
          | Exp.Subtract (Exp.Var _, IConst (i, _), _) ->
                i>=0, i>=0, true
          | Exp.Subtract (IConst (i,_),Exp.Var _, _) ->
               i!=0, i!=0, true
          | _ -> false, false, false
      end
    | Gt (Exp.Var _, e2, _) | Lt (e2, Exp.Var _, _)  -> begin
        match e2 with
          | Exp.Var _ -> true, true, true
          | Exp.Add (Exp.Var _, IConst (i, _), _)
          | Exp.Add ( IConst (i, _), Exp.Var _, _) ->
                i<=0, i>=0, true
          | Exp.Subtract (Exp.Var _, IConst (i, _), _) ->
                 i<=0, i<=0, true
          | Exp.Subtract (IConst (i, _) ,Exp.Var _, _) ->
                i!=0, i!=0, true
          | _ -> false, false, false
      end
    | Lte (Exp.Var _, e2, _) | Gte (e2, Exp.Var _, _) ->  begin
        match e2 with
          | Exp.Var _ -> true, false, true
          | Exp.Add (Exp.Var _, IConst (i,_), _) | Exp.Add ( IConst (i,_), Exp.Var _, _) -> i<0, i<0, true
          | Exp.Subtract (Exp.Var _, IConst (i, _), _) -> i>0, i>0, true
          | Exp.Subtract (IConst (i, _),Exp.Var _, _) -> i!=0, i!=0, true
          | _ -> false, false, false
      end
    | Gte (Exp.Var _, e2, _) | Lte (e2, Exp.Var _, _)  -> begin
        match e2 with
          | Exp.Var _ -> true, false, true
          | Exp.Add (Exp.Var _, IConst (i,_), _) | Exp.Add ( IConst (i,_), Exp.Var _, _) ->  i>0, i>0, true
          | Exp.Subtract (Exp.Var _, IConst (i, _), _) -> i<0, i<0, true
          | Exp.Subtract (IConst (i, _),Exp.Var _, _) -> i!=0, i!=0, true
          | _ -> false, false, false
      end
    | Eq (Exp.Var _, e2, _) -> begin
        match e2 with
          | Exp.Var _ -> false, false, false
          | Exp.Add (Exp.Var _, e3, _) | Exp.Add ( e3, Exp.Var _, _)
          | Exp.Subtract (Exp.Var _, e3, _) | Exp.Subtract (e3, Exp.Var _, _) -> begin
              match e3 with
                | IConst (i, _) -> false, i!=0, true
                | _ -> false, false, false
            end
          | _ -> false, false, false
      end
    | _ -> false, false, false

let is_rel a0=
  match a0 with
    | RelForm _ -> true
    | _ -> false

let decompose_rel a0=
  match a0 with
    | RelForm (id_name, esv, _) -> (id_name, Exp.afv_list esv)
    | _ -> raise Not_found
