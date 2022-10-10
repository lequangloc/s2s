
open Globals
open Gen.Basic
open VarGen


type exp =
  | Ann_Exp of (exp * typ * loc)
  | Null of loc
  | Var of ((ident * primed) * loc)
(* variables could be of type pointer, int, bags, lists etc *)
  | IConst of (int * loc)
  | FConst of (float * loc)
  | SConst of (ident * loc )
  | CConst  of (int * loc)
  | Add of (exp * exp * loc)
  | Subtract of (exp * exp * loc)
  | Mult of (exp * exp * loc)
  | Div of (exp * exp * loc)
  | Max of (exp * exp * loc)
  | Min of (exp * exp * loc)
(* bag expressions *)
  | Bag of (exp list * loc)
  | BagUnion of (exp list * loc)
  | BagIntersect of (exp list * loc)
  | BagDiff of (exp * exp * loc)
  | TypeCast of (typ * exp * loc)
  | ArrayAt of ((ident * primed) * (exp list) * loc)
       (*String expressions*)
  (* | Sleng of (Var.t * loc) *)
  | Concat of (exp * exp * loc)


and t = exp


let rec string_of e=match e with
  | Ann_Exp (e,t,l) -> "(" ^ (string_of e)^":"^(string_of_typ t) ^ ")"
  | Null p -> "null"
  | Var  ((v, p),  _) -> v ^
        (match p with | Primed -> "'" | Unprimed -> "" )
  | IConst (i,p) -> string_of_int i
  | FConst (f, p) -> ""
  | SConst (id, p) -> id
  | CConst (c, p) -> "\'" ^ (String.make 1 (Char.chr c)) ^ "\'" 
  | Add (e1, e2, p) -> "(" ^ (string_of e1) ^ "+" ^ (string_of e2) ^ ")"
  | Subtract (e1, e2, p) -> "(" ^ (string_of e1) ^ "-" ^ (string_of e2) ^ ")"
  | Mult (e1, e2, p) -> "(" ^ (string_of e1) ^ "*" ^ (string_of e2) ^ ")"
  | Div (e1, e2, p) -> "(" ^ (string_of e1) ^ ":" ^ (string_of e2) ^ ")"
  | Max (e1, e2, p) -> "max(" ^ (string_of e1) ^ "," ^ (string_of e2) ^ ")"
  | Min (e1, e2, p) -> "min(" ^ (string_of e1) ^ "," ^ (string_of e2) ^ ")"
        (* bag expressions *)
  | Bag _
  | BagUnion _
  | BagIntersect _
  | BagDiff _ -> "bag"
  | TypeCast _ -> "TypeCast"
  | ArrayAt _ -> "ArrayAt"
        (*String expressions*)
  | Concat (e1, e2, p) -> (string_of e1) ^ " . " ^ (string_of e2)

let rec typ_of_exp (e: t) : typ =
  let pos = no_pos in
  let merge_types typ1 typ2 =
    if (typ1 = UNK) then typ2
    else if (typ1 = typ2) then typ1
    else match typ2  with
      | UNK -> typ1
      | _ -> Gen.Basic.report_error pos "Ununified type in 2 expressions"
  in
  match e with
  | Ann_Exp (ex, ty, _)       -> let ty2 = typ_of_exp ex in
    merge_types ty2 ty
  | Null _                    -> Globals.UNK
  | Var  _                    -> Globals.UNK
        (* Const *)
  | IConst _                  -> Globals.Int
  | FConst _                  -> Globals.Float
  | SConst _
  | CConst  _ -> Globals.String
        (* Arithmetic expressions *)
  | Add (ex1, ex2, _)
  | Subtract (ex1, ex2, _)
  | Mult (ex1, ex2, _)
  | Div (ex1, ex2, _)
  | Max (ex1, ex2, _)
  | Min (ex1, ex2, _)         -> let ty1 = typ_of_exp ex1 in
    let ty2 = typ_of_exp ex2 in
    merge_types ty1 ty2
        (* bag expressions *)
  | Bag (ex_list, _)
  | BagUnion (ex_list, _)
  | BagIntersect (ex_list, _) -> let ty_list = List.map typ_of_exp ex_list in 
    let ty = List.fold_left merge_types UNK ty_list in
    Globals.BagT ty
  | BagDiff (ex1, ex2, _)     -> let ty1 = typ_of_exp ex1 in
    let ty2 = typ_of_exp ex2 in
    let ty = merge_types ty1 ty2 in
    Globals.BagT ty
  | TypeCast (ty, ex1, _)     -> ty
        (* Array expressions *)
  | ArrayAt (_, ex_list, _)   ->
    let ty_list = List.map typ_of_exp ex_list in
    let ty = List.fold_left merge_types UNK ty_list in
    let len = List.length ex_list in
    Globals.Array (ty, len)
  | Concat _ ->  Globals.String

let mkAnnExp e t pos = Ann_Exp (e,t,pos)

let mkNull p = Null p

let mkVar v p = Var (v, p)

let mkIConst i p = IConst(i, p)

let mkFConst f p = FConst(f, p)

let mkSConst id p = SConst(id, p)

let mkCConst c p = CConst(c, p)

let mkAdd e1 e2 p = Add (e1, e2, p)

let mkSubtract e1 e2 p = Subtract (e1, e2, p)

let mkMult e1 e2 p = Mult (e1, e2, p)

let mkDiv e1 e2 p = Div (e1, e2, p)

let mkMax e1 e2 p = Max (e1, e2, p)

let mkMin e1 e2 p = Min (e1, e2, p)

let mkBag es p = Bag (es, p)

let mkBagUnion es p = BagUnion (es, p)

let mkBagIntersect es p = BagIntersect (es, p)

let mkBagDiff e1 e2 p = BagDiff (e1, e2, p)

let mkTypeCast t e pos = TypeCast (t,e, pos)

let mkArrayAt id es pos = ArrayAt(id, es, pos)

let mkConcat e1 e2 p = Concat (e1, e2, p)

let rec combine_vars (a1 : t) (a2 : t) : (ident * primed) list =
  let fv1 = fv a1 in
  let fv2 = fv a2 in
  Gen.BList.remove_dups_eq (=) (fv1 @ fv2)

and fv (af : t) : (ident * primed) list = match af with
  | Var (sv, _) ->
        let id = fst sv in
        if (id.[0] = '#') then [] else [sv]
  | Null _
  | IConst _
  | SConst _
  | CConst _
  | FConst _ -> []
  | Ann_Exp (e,_,_) -> fv e
  | Add (a1, a2, _)  | Subtract (a1, a2, _)
  | Mult (a1, a2, _) | Div (a1, a2, _) -> combine_vars a1 a2
  | Max (a1, a2, _) -> combine_vars a1 a2
  | Min (a1, a2, _) -> combine_vars a1 a2
  | TypeCast (_, a, _) -> fv a
  | BagDiff (a1,a2,_) ->  combine_vars a1 a2
  | Bag(d,_)
  | BagIntersect (d,_)
  | BagUnion (d,_) ->  Gen.BList.remove_dups_eq (=)
        (List.fold_left (fun a c-> a@(fv c)) [] d)
  | ArrayAt (a, i, _) ->
    let ifv = List.flatten (List.map fv i) in
    Gen.BList.remove_dups_eq (=) (a :: ifv)

  | Concat (a1, a2, _) -> combine_vars a1 a2


let fresh_var (sv : (ident*primed)):(ident*primed) =
  let old_name = fst sv in
  let name = fresh_old_name old_name in
  (name, Unprimed)

let fresh_vars (svs : (ident*primed) list):(ident*primed) list =
  List.map fresh_var svs

let eq_var (id1, p1) (id2, p2):bool =
  ((String.compare id1 id2)==0) && p1==p2

let v_apply_one ((fr, t)) v = (if eq_var v fr then t else v)

let rec e_apply_one ((fr, t) as p) e = match e with
  | Null _
  | IConst _
  | FConst _ | SConst _ | CConst _-> e
  | Ann_Exp (e,ty,pos) -> Ann_Exp ((e_apply_one p e), ty, pos)
  | Var (sv, pos) -> Var (v_apply_one p sv, pos)
  | Add (a1, a2, pos) -> Add (e_apply_one p a1, e_apply_one p a2, pos)
  | Subtract (a1, a2, pos) -> Subtract (e_apply_one p a1, e_apply_one p a2, pos)
  | Mult (a1, a2, pos) -> Mult (e_apply_one p a1, e_apply_one p a2, pos)
  | Div (a1, a2, pos) -> Div (e_apply_one p a1, e_apply_one p a2, pos)
  | Max (a1, a2, pos) -> Max (e_apply_one p a1, e_apply_one p a2, pos)
  | Min (a1, a2, pos) -> Min (e_apply_one p a1, e_apply_one p a2, pos)
  | TypeCast (ty, a1, pos) -> TypeCast (ty, e_apply_one p a1, pos)
  | Bag (alist, pos) -> Bag ((e_apply_one_list p alist), pos)
  | BagUnion (alist, pos) -> BagUnion ((e_apply_one_list p alist), pos)
  | BagIntersect (alist, pos) -> BagIntersect ((e_apply_one_list p alist), pos)
  | BagDiff (a1, a2, pos) -> BagDiff (e_apply_one p a1, e_apply_one p a2, pos)
  | ArrayAt (a, ind, pos) -> ArrayAt (v_apply_one p a, (e_apply_one_list p ind), pos)
  | Concat (a1, a2, pos) -> Concat (e_apply_one p a1, e_apply_one p a2, pos)


and e_apply_one_list ((fr, t) as p) alist = match alist with
  |[] -> []
  |a :: rest -> (e_apply_one p a) :: (e_apply_one_list p rest)
