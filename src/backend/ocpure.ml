open Globals

open Cpure
open Term
open Exp
open Var


type relation = (* for obtaining back results from Omega Calculator. *)
  | ConstRel of bool
  | BaseRel of (Exp.t list * Cpure.t)
  | UnionRel of (relation * relation)


(* build relation from list of expressions, for example a,b,c < d,e, f *)
and build_relation relop alist10 alist20 lbl pos =
  let prt = fun al -> List.fold_left (fun r a -> r ^ "; " ^ (Exp.string_of a)) "" al in
  Debug.no_2 "build_relation" prt prt (Cpure.string_of) (fun al1 al2 -> build_relation_x relop al1 al2 lbl pos) alist10 alist20

and build_relation_x relop alist10 alist20 lbl pos =
  let rec helper1 ae alist =
    (* print_endline "inside helper1"; *)
    let a = List.hd alist in
    let rest = List.tl alist in
    let rec tt relop ae a pos = 
      let r = (relop ae a pos) in
      r in
    
    let tmp = BForm (((tt relop ae a pos), None),lbl) in
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

