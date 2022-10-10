
open Globals
open Gen.Basic
open VarGen


type term=
  | BConst of (bool * loc)
  | BVar of ((ident * primed) * loc)
  | Lt of (Iexp.t * Iexp.t * loc)
  | Lte of (Iexp.t * Iexp.t * loc)
  | Gt of (Iexp.t * Iexp.t * loc)
  | Gte of (Iexp.t * Iexp.t * loc)
(* these two could be arithmetic or pointer or bags or lists *)
  | Eq of (Iexp.t * Iexp.t * loc)
  | Neq of (Iexp.t * Iexp.t * loc)
  | EqMax of (Iexp.t * Iexp.t * Iexp.t * loc) (* first is max of second and third *)
  | EqMin of (Iexp.t * Iexp.t * Iexp.t * loc) (* first is min of second and third *)
  (* bags and bag formulae *)
  | BagIn of ((ident * primed) * Iexp.t * loc)
  | BagNotIn of ((ident * primed) * Iexp.t * loc)
  | BagSub of (Iexp.t * Iexp.t * loc)
  | BagMin of ((ident * primed) * (ident * primed) * loc)
  | BagMax of ((ident * primed) * (ident * primed) * loc)
(*Relational formula to capture relations, for instance, s(a,b,c) or t(x+1,y+2,z+3), etc. *)
  | RelForm of (ident * (Iexp.t list) * loc)

type t = term


let rec string_of t=
  match t with
    | BConst (b, p) -> string_of_bool b
    | BVar ((id, p), l) -> begin id ^ (
        match p with
          | Primed -> "'"
          | Unprimed -> ""
      )
      end
    | Lt (e1, e2, p) -> (Iexp.string_of e1) ^ "<"
          ^ (Iexp.string_of e2)
    | Lte (e1, e2, p) -> (Iexp.string_of e1) ^ "<="
          ^ (Iexp.string_of e2)
    | Gt (e1, e2, p) -> (Iexp.string_of e1) ^ ">"
          ^ (Iexp.string_of e2)
    | Gte (e1, e2, p) -> (Iexp.string_of e1) ^ ">="
          ^ (Iexp.string_of e2)
    | Eq (e1, e2, p) -> (Iexp.string_of e1) ^ "="
          ^ (Iexp.string_of e2)
    | Neq (e1, e2, p) -> (Iexp.string_of e1) ^ "!="
          ^ (Iexp.string_of e2)
    | EqMax (e1, e2, e3, p) -> "EqMax"
    | EqMin (e1, e2, e3, p) -> "EqMin"
          (* bag formulas *)
    | BagIn (sv, e, p) -> "BagIn"
    | BagNotIn (sv, e, p) -> "BagNotIn"
    | BagSub (e1, e2, p) -> "BagSub"
    | BagMin (e1, e2, p) -> "BagMin"
    | BagMax (e1, e2, p) -> "BagMax"
          (*string logic*)
    | RelForm _ -> "RelForm"


let mkTrue p = BConst (true, p)

let mkFalse p = BConst (false, p)

let isConstTrue t = match t with
  | BConst (true, _) -> true
  | _ -> false

let isConstFalse t = match t with
  | BConst (false, _) -> true
  | _ -> false

let mkBVar (v, p) pos = BVar ((v, p), pos)

let mkLt e1 e2 pos = Lt (e1, e2, pos)

let mkLte e1 e2 pos = Lte (e1, e2, pos)

let mkGt e1 e2 pos = Gt (e1, e2, pos)

let mkGte e1 e2 pos = Gte (e1, e2, pos)

let mkEq e1 e2 pos = Eq (e1, e2, pos)

let mkNeq e1 e2 pos = Neq (e1, e2, pos)

let mkEqMax e1 e2 e3 pos = EqMax (e1, e2, e3, pos)

let mkEqMin e1 e2 e3 pos = EqMin (e1, e2, e3, pos)

let mkBagIn v e pos = BagIn (v, e, pos)

let mkBagNotIn v e pos = BagNotIn (v, e, pos)

let mkBagSub e1 e2 pos = BagSub (e1, e2, pos)

let mkBagMin v1 v2 pos = BagMin (v1, v2, pos)

let mkBagMax v1 v2 pos = BagMax (v1, v2, pos)

let mkRelForm id exps pos = RelForm(id, exps, pos)

let fv (pf: t)= match pf with
    | BConst _ -> []
    | BVar (bv, _) -> [bv]
    | Lt (a1, a2, _) | Lte (a1, a2, _)
    | Gt (a1, a2, _) | Gte (a1, a2, _)
    | Eq (a1, a2, _) | Neq (a1, a2, _) -> Iexp.combine_vars a1 a2
    | EqMax (a1, a2, a3, _) ->
          let fv1 = Iexp.fv a1 in
          let fv2 = Iexp.fv a2 in
          let fv3 = Iexp.fv a3 in
          Gen.BList.remove_dups_eq (=) (fv1 @ fv2 @ fv3)
    | EqMin (a1, a2, a3, _) ->
          let fv1 = Iexp.fv a1 in
          let fv2 = Iexp.fv a2 in
          let fv3 = Iexp.fv a3 in
          Gen.BList.remove_dups_eq (=) (fv1 @ fv2 @ fv3)
  | BagIn (v, a, _) ->
        let fv = Iexp.fv a in
        Gen.BList.remove_dups_eq (=) ([v] @ fv)
  | BagNotIn (v, a, _) ->
        let fv = Iexp.fv a in
        Gen.BList.remove_dups_eq (=) ([v] @ fv)
  | BagSub (a1, a2, _) -> Iexp.combine_vars a1 a2
  | BagMax (sv1, sv2, _) -> Gen.BList.remove_dups_eq (=) ([sv1] @ [sv2])
  | BagMin (sv1, sv2, _) -> Gen.BList.remove_dups_eq (=) ([sv1] @ [sv2])
  | RelForm (_,args,_) ->
    let args_fv = List.concat (List.map Iexp.fv args) in
    Gen.BList.remove_dups_eq (=) args_fv


let apply_one ((fr, t) as p) pf = match pf with
  | BConst _ -> pf
  | BVar (bv, pos) -> BVar (Iexp.v_apply_one p bv, pos)
  | Lt (a1, a2, pos) -> Lt (Iexp.e_apply_one (fr, t) a1,
                            Iexp.e_apply_one (fr, t) a2, pos)
  | Lte (a1, a2, pos) -> Lte (Iexp.e_apply_one (fr, t) a1,
                              Iexp.e_apply_one (fr, t) a2, pos)
  | Gt (a1, a2, pos) -> Gt (Iexp.e_apply_one (fr, t) a1,
                            Iexp.e_apply_one (fr, t) a2, pos)
  | Gte (a1, a2, pos) -> Gte (Iexp.e_apply_one (fr, t) a1,
                              Iexp.e_apply_one (fr, t) a2, pos)
  | Eq (a1, a2, pos) -> Eq (Iexp.e_apply_one (fr, t) a1,
                            Iexp.e_apply_one (fr, t) a2, pos)
  | Neq (a1, a2, pos) -> Neq (Iexp.e_apply_one (fr, t) a1,
                              Iexp.e_apply_one (fr, t) a2, pos)
  | EqMax (a1, a2, a3, pos) -> EqMax (Iexp.e_apply_one (fr, t) a1,
                                      Iexp.e_apply_one (fr, t) a2,
                                      Iexp.e_apply_one (fr, t) a3, pos)
  | EqMin (a1, a2, a3, pos) -> EqMin (Iexp.e_apply_one (fr, t) a1,
                                      Iexp.e_apply_one (fr, t) a2,
                                      Iexp.e_apply_one (fr, t) a3, pos)
  | BagIn (v, a1, pos) -> BagIn (Iexp.v_apply_one p v, Iexp.e_apply_one (fr, t) a1, pos)
  | BagNotIn (v, a1, pos) -> BagNotIn (Iexp.v_apply_one p v, Iexp.e_apply_one (fr, t) a1, pos)
  | BagSub (a1, a2, pos) -> BagSub (Iexp.e_apply_one (fr, t) a1, Iexp.e_apply_one (fr, t) a2, pos)
  | BagMax (v1, v2, pos) -> BagMax (Iexp.v_apply_one p v1, Iexp.v_apply_one p v2, pos)
  | BagMin (v1, v2, pos) -> BagMin (Iexp.v_apply_one p v1, Iexp.v_apply_one p v2, pos)
  | RelForm (r, args, pos) ->
        RelForm (r, (List.map (fun x -> Iexp.e_apply_one (fr, t) x) args), pos)
