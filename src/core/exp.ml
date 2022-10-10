open Globals
open Gen
open VarGen

open Var


type exp =
  | Null of loc
  | Var of (Var.t * loc)
  | IConst of (int * loc)
  | FConst of (float * loc)
  | SConst of (ident * loc)
  | CConst of (int * loc)
  | Add of (exp * exp * loc)
  | Subtract of (exp * exp * loc)
  | Mult of (exp * exp * loc)
  | Div of (exp * exp * loc)
  | Max of (exp * exp * loc)
  | Min of (exp * exp * loc)
  | TypeCast of (typ * exp * loc)
        (* bag expressions *)
  | Bag of (exp list * loc)
  | BagUnion of (exp list * loc)
  | BagIntersect of (exp list * loc)
  | BagDiff of (exp * exp * loc)
  | ArrayAt of (Var.t * (exp list) * loc)
        (*String expressions*)
  (* | Sleng of (Var.t * loc) *)
  | Concat of (exp * exp * loc)

type t = exp

let is_concat e = match e with
  | Concat _ -> true
  | _ -> false


let rec string_of e =match e with
  | Null p -> "null" (*^ (string_of_pos p)*)
  | Var  (v,  p) -> Var.string_of v
  | IConst (i,p) -> string_of_int i
  | FConst (f, p) -> ""
  | SConst (id, p) -> id
  | CConst (c, p) -> "\'" ^ (String.make 1 (Char.chr c)) ^ "\'" 
  | Add (e1, e2, p) -> "(" ^ (string_of e1) ^ "+" ^ (string_of e2) ^ ")"
  | Subtract (e1, e2, _) -> "(" ^ (string_of e1) ^ "-" ^ (string_of e2) ^ ")"
  | Mult (e1, e2, _) -> "(" ^ (string_of e1) ^ "*" ^ (string_of e2) ^ ")"
  | Div (e1, e2, _) -> "(" ^ (string_of e1) ^ ":" ^ (string_of e2) ^ ")"
  | Max (e1, e2, _) -> "max(" ^ (string_of e1) ^ "," ^ (string_of e2) ^ ")"
  | Min (e1, e2, _) -> "min(" ^ (string_of e1) ^ "," ^ (string_of e2) ^ ")"
  | TypeCast (ty, e1 , _) -> ("(" ^ (Globals.string_of_typ ty) ^ ")");
    string_of e1;
        (* bag expressions *)
  | Bag _
  | BagUnion _
  | BagIntersect _
  | BagDiff _ -> "bag"
  | ArrayAt _ -> "ArrayAt"
        (*String expressions*)
  | Concat (e1, e2, p) -> (string_of e1) ^ " . " ^ (string_of e2)


let is_string_exp e = match e with
  | Null _ -> false
  | Var (sv, _) -> sv.t == String
  | IConst _
  | FConst _ -> false
  | SConst _ | CConst _ -> true
  | Add _ 
  | Subtract _
  | Mult _
  | Div _
  | Max _
  | Min _
  | TypeCast _
        (* bag expressions *)
  | Bag _
  | BagUnion _
  | BagIntersect _
  | BagDiff _
  | ArrayAt _ -> false
        (*String expressions*)
  | Concat _ -> true


let rec is_arith_exp e= match e with
  | Null _ -> false
  | Var (sv, _) -> sv.t == Int
  | IConst _ -> true
  | FConst _
  | SConst _ | CConst _ | TypeCast _ -> false
  | Add (e1, e2, _)
  | Subtract (e1, e2, _)
  | Mult (e1, e2, _)
  | Div (e1, e2, _)
  | Max (e1, e2, _)
  | Min (e1, e2, _) -> (is_arith_exp e1) && (is_arith_exp e2)
        (* bag expressions *)
  | Bag _
  | BagUnion _
  | BagIntersect _
  | BagDiff _ | ArrayAt _ -> false
        (*String expressions*)
  | Concat _ -> false


let is_string_var e= match e with
  | Var (sv, _) -> sv.t == String
  | _ -> false

let rec is_string_const e= match e with
  | SConst _ | CConst _ -> true
  | Concat (e1, e2, _) -> (is_string_const e1) && (is_string_const e2)
  | _ -> false


let is_null e = match e with
  | Null _ -> true
  | _ -> false

let rec combine_avars a1 a2 : Var.t list =
  let fv1 = fv a1 in
  let fv2 = fv a2 in
  let svs = (fv1 @ fv2) in
  svs

and fv ?(dups=false) af =
  let rec helper af0= match af0 with
    | Null _ 
    | IConst _ 
    | SConst _ | CConst _
    | FConst _ -> []
    | Var (sv, _) -> [sv]
    | Add (a1, a2, _) -> combine_avars a1 a2
    | Subtract (a1, a2, _) -> combine_avars a1 a2
    | Mult (a1, a2, _) | Div (a1, a2, _) -> combine_avars a1 a2
    | Max (a1, a2, _) -> combine_avars a1 a2
    | Min (a1, a2, _) -> combine_avars a1 a2
    | TypeCast (_, e1, _) -> fv e1
    | Bag (alist, _) -> let svlist = afv_list alist in
       (* remove_dups *) svlist
    | BagUnion (alist, _) -> let svlist = afv_list alist in
       (* remove_dups *) svlist
    | BagIntersect (alist, _) -> let svlist = afv_list alist in
      (* remove_dups *) svlist
    | BagDiff(a1, a2, _) -> combine_avars a1 a2
    | ArrayAt  (v , es, _ ) -> [v]@(List.fold_left ( fun r e -> r@(helper e)) [] es)
    | Concat (a1, a2, _) -> combine_avars a1 a2
  in
  let svl = helper af in
  if not dups then remove_dups svl else
    svl


and afv_list (alist : exp list) :  Var.t list = match alist with
  |[] -> []
  |a :: rest -> fv a @ afv_list rest

let mkVar sv pos= Var (sv, pos)

let mkIConst a pos = IConst (a, pos)

let mkCConst a pos = CConst (a, pos)

let mkN n pos =  IConst (n, pos)

let mkZero pos = mkN 0 pos

let is_zero b =   match b with
  | IConst(0,_) -> true
  | _ -> false

let is_one b =   match b with
  | IConst(1,_) -> true
  | _ -> false

let mkEmpCConst pos =
  let a = Char.code semp in
  CConst (a, pos)

let isEmpCConst e =
  match e with
    | CConst (a, _) -> a == Char.code semp
    | _ -> false

let mkConcatExp e1 e2 pos = Concat (e1, e2, pos)

let rec eqExp_f (eq:Var.t -> Var.t -> bool) (e1:t)(e2:t):bool =
  (* Debug.no_2 "eqExp_f" !print_exp !print_exp string_of_bool *) (eqExp_f_x eq) e1 e2 

and eqExp_list_f (eq:Var.t -> Var.t -> bool) (e1 : t list) (e2 : t list) : bool =
  let rec eq_exp_list_helper (e1 : t list) (e2 : t list) = match e1 with
    | [] -> true
    | h :: t -> (List.exists (fun c -> eqExp_f eq h c) e2) && (eq_exp_list_helper t e2)
  in
  (eq_exp_list_helper e1 e2) && (eq_exp_list_helper e2 e1)


and eqExp_f_x (eq:Var.t -> Var.t -> bool) (e1:t)(e2:t):bool =
  let rec helper e1 e2 =
    match (e1, e2) with
    | (Null(_), Null(_)) -> true
    | (Null(_), Var(sv, _)) -> (name_of sv) = "null"
    | (Var(sv, _), Null(_)) -> (name_of sv) = "null"
    | (Var(sv1, _), Var(sv2, _)) -> (eq sv1 sv2)
    | (IConst(i1, _), IConst(i2, _)) -> i1 = i2
    | (FConst(f1, _), FConst(f2, _)) -> f1 = f2
    | (SConst(f1, _), SConst(f2, _)) -> f1 = f2
    | (CConst(f1, _), CConst(f2, _)) -> f1 = f2
    | (Subtract(e11, e12, _), Subtract(e21, e22, _))
    | (Max(e11, e12, _), Max(e21, e22, _))
    | (Min(e11, e12, _), Min(e21, e22, _))
    | (Add(e11, e12, _), Add(e21, e22, _)) -> (helper e11 e21) && (helper e12 e22)
    | (Mult(e11, e12, _), Mult(e21, e22, _)) -> (helper e11 e21) && (helper e12 e22)
    | (Div(e11, e12, _), Div(e21, e22, _)) -> (helper e11 e21) && (helper e12 e22)
    | (Bag(e1, _), Bag(e2, _))
    | (BagUnion(e1, _), BagUnion(e2, _))
    | (BagIntersect(e1, _), BagIntersect(e2, _)) -> (eqExp_list_f eq e1 e2)
    | (BagDiff(e1, e2, _), BagDiff(e3, e4, _)) -> (helper e1 e3) && (helper e2 e4)
    | (Concat(e11, e12, _), Concat(e21, e22, _)) -> (helper e11 e21) && (helper e12 e22)
    | _ -> false
  in helper e1 e2

let rec elim_semp_x e=
  match e with
    | Concat (e1, e2, p) -> begin
        let n_e1 = elim_semp_x e1 in
        let n_e2 = elim_semp_x e2 in
        if isEmpCConst n_e1 then
          n_e2
        else if isEmpCConst n_e2 then
          n_e1
        else Concat (n_e1, n_e2, p)
      end
    | _ -> e

and elim_semp e=
  Debug.no_1 "elim_semp" string_of string_of
      (fun _ -> elim_semp_x e) e

let rec subst_one_term ((fr, t) : (Var.t * t)) e = match e with
  | Null _ 
  | IConst _ 
  | SConst _ | CConst _
  | FConst _ -> e
  | Add (a1, a2, pos) -> (Add (subst_one_term (fr, t) a1, subst_one_term (fr, t) a2, pos))
  | Subtract (a1, a2, pos) -> Subtract (subst_one_term (fr, t) a1, subst_one_term (fr, t) a2, pos)
  | Mult (a1, a2, pos) -> Mult (subst_one_term (fr, t) a1, subst_one_term (fr, t) a2, pos)
  | Div (a1, a2, pos) -> Div (subst_one_term (fr, t) a1, subst_one_term (fr, t) a2, pos)
  | Var (sv, pos) -> if equal sv fr then t else e
  | Max (a1, a2, pos) -> Max (subst_one_term (fr, t) a1, subst_one_term (fr, t) a2, pos)
  | Concat (a1, a2, pos) -> elim_semp (Concat (subst_one_term (fr, t) a1, subst_one_term (fr, t) a2, pos))
  | Min (a1, a2, pos) -> Min (subst_one_term (fr, t) a1, subst_one_term (fr, t) a2, pos)
  | TypeCast (ty, a, pos) -> TypeCast (ty, subst_one_term (fr, t) a, pos)
  | Bag (alist, pos) -> Bag ((subst_one_term_list (fr, t) alist), pos)
  | BagUnion (alist, pos) -> BagUnion ((subst_one_term_list (fr, t) alist), pos)
  | BagIntersect (alist, pos) -> BagIntersect ((subst_one_term_list (fr, t) alist), pos)
  | BagDiff (a1, a2, pos) -> BagDiff (subst_one_term (fr, t) a1, subst_one_term (fr, t) a2, pos)
  | ArrayAt (a, i, pos) -> ArrayAt (a, subst_one_term_list (fr, t) i, pos)

and subst_one_term_list (fr, t) alist = match alist with
  |[] -> []
  |a :: rest -> (subst_one_term (fr, t) a) :: (subst_one_term_list (fr, t) rest)

let subst sst e=
  List.fold_left (fun r (fr, sv) ->
      let e_sv = Var (sv, no_pos) in
      subst_one_term (fr, e_sv) r
  ) e sst

let subst_type t_sst e0=
  let rec aux e= match e with
  | Null _ | IConst _ | SConst _ | CConst _ | FConst _ -> e
  | Add (a1, a2, pos) -> (Add (aux a1, aux a2, pos))
  | Subtract (a1, a2, pos) -> Subtract (aux a1, aux a2, pos)
  | Mult (a1, a2, pos) -> Mult (aux a1, aux a2, pos)
  | Div (a1, a2, pos) -> Div (aux a1, aux a2, pos)
  | Var (sv, pos) -> Var (Var.subst_type t_sst sv, pos)
  | Max (a1, a2, pos) -> Max (aux a1, aux a2, pos)
  | Concat (a1, a2, pos) -> (Concat (aux a1, aux a2, pos))
  | Min (a1, a2, pos) -> Min (aux a1, aux a2, pos)
  | TypeCast (ty, a, pos) -> TypeCast (ty, aux a, pos)
  | Bag (alist, pos) -> Bag ((List.map aux alist), pos)
  | BagUnion (alist, pos) -> BagUnion ((List.map aux alist), pos)
  | BagIntersect (alist, pos) -> BagIntersect ((List.map aux alist), pos)
  | BagDiff (a1, a2, pos) -> BagDiff (aux a1, aux a2, pos)
  | ArrayAt (a, i, pos) -> ArrayAt (a, List.map aux i, pos)
  in aux e0

let rec flatten_concat_x e res=
  match e with
    | Concat (e1, e2, _) ->
          let r1 = flatten_concat_x e2 res in
          flatten_concat_x e1 r1
    |_ -> [e]@res

and flatten_concat e res=
  let pr1 = pr_list string_of in
  Debug.no_2 "flatten_concat" string_of pr1 pr1
      (fun _ _ -> flatten_concat_x e res) e res

let rec combine_concat fst rest p=
  match rest with
    | [] -> fst
    | x::es -> let r = combine_concat x es p in
      Concat (fst , r, p)

let normalize_concat e =
  match e with
    | Concat (_,_, p) -> begin
        let es = flatten_concat e [] in
        match es with
          | [] -> raise (Invalid_argument "exp.normalize_concat")
          | fst::rest ->
                combine_concat fst rest p
      end
    | _ -> e


let rec string_to_length_x e=
  match e with
    | CConst (_, p) -> let i = if isEmpCConst e then 0 else 1 in
      IConst (i, p)
    | Var (sv , p) ->
          let () = Debug.ninfo_hprint (add_str  "sv.Var.id" pr_id) sv.Var.id no_pos in
          let sv_int = Globals.lookup_sleng sv.Var.id in
          let () = Debug.ninfo_hprint (add_str  "sv_int" pr_id) sv_int no_pos in
          Var ({Var.t= Int; Var.id = sv_int; Var.p = sv.Var.p}, p)
    | Concat (e1, e2, p) ->
          let n_e1 = string_to_length_x e1 in
          let n_e2 = string_to_length_x e2 in
          Add (n_e1, n_e2, p)
    | _ -> raise (Invalid_argument "Exp.string_to_length")

and string_to_length e=
  Debug.no_1 "Exp.string_to_length" string_of string_of
      (fun _ -> string_to_length_x e) e

let rec get_cconst_x e res=
  match e with
    | CConst _ -> res@[e]
    | Concat (e1, e2,_) -> let r1 = get_cconst_x e1 res in
      get_cconst_x e2 r1
    | _ -> res

let get_cconst e=
  Debug.no_1 "Exp.get_cconst" string_of (pr_list string_of)
      (fun _ -> get_cconst_x e []) e

let mkAdd_list es pos=
 match es with
   | hd::tl ->
         List.fold_left (fun r e->
             Add (r, e, pos)
         ) hd tl
   | [] -> raise (Invalid_argument "exp.mkAdd_list")

let rec simp_mult_x (e : exp) :  exp =
  let rec normalize_add m lg (x: exp):  exp =
    match x with
    |  Add (e1, e2, l) ->
      let t1 = normalize_add m l e2 in normalize_add (Some t1) l e1
    | _ -> (match m with | None -> x | Some e ->  Add (e, x, lg)) in
  let rec acc_mult m e0 =
    match e0 with
    | Null _ | SConst _ | CConst _ -> e0
    | Var (v, l) ->
      (match m with
       | None -> e0
       | Some c ->  Mult (IConst (c, l), e0, l))
    | IConst (v, l) ->
          (match m with
            | None -> e0
            | Some c ->  IConst (c * v, l))
    | FConst (v, l) ->
      (match m with
       | None -> e0
       | Some c -> FConst (v *. (float_of_int c), l))
    |  Add (e1, e2, l) ->
           normalize_add None l ( Add (acc_mult m e1, acc_mult m e2, l))
    |  Subtract (e1, e2, l) ->
           normalize_add None l
               ( Add (acc_mult m e1,
               acc_mult
                   (match m with | None -> Some (- 1) | Some c -> Some (- c)) e2,
               l))
    | Mult (e1, e2, l) -> Mult (acc_mult m e1, acc_mult None e2, l)
    | Div (e1, e2, l) -> Div (acc_mult m e1, acc_mult None e2, l)
    |  Max (e1, e2, l) ->
           Error.report_error
               {
                   Error.error_loc = l;
                   Error.error_text =
                       "got Max !! (Should have already been simplified )";
               }
    |  Min (e1, e2, l) ->
           Error.report_error
               {
                   Error.error_loc = l;
                   Error.error_text =
                       "got Min !! (Should have already been simplified )";
               }
    | TypeCast (ty, e1, l) -> TypeCast (ty, acc_mult m e1, l)
    |  Bag (el, l) ->  Bag (List.map (acc_mult m) el, l)
    |  BagUnion (el, l) ->  BagUnion (List.map (acc_mult m) el, l)
    |  BagIntersect (el, l) -> BagIntersect (List.map (acc_mult m) el, l)
    |  BagDiff (e1, e2, l) -> BagDiff (acc_mult m e1, acc_mult m e2, l)
    | ArrayAt (a, i, pos) -> ArrayAt (a, List.map (acc_mult m) i, pos)
    | Concat (e1, e2, l) -> Concat (acc_mult m e1, acc_mult m e2, l)
  in acc_mult None e

and simp_mult (e: exp) : exp =
  let pr = string_of in
  Debug.no_1 "simp_mult" pr pr simp_mult_x e

let rec split_sums (e : t) : (( t option) * (t option)) =
  let pr1 = pr_opt string_of in
  (* Debug.no_1 "split_sums" !print_exp (pr_pair pr1 pr1) *)
    split_sums_x e

and split_sums_x (e :  exp) : (( exp option) * ( exp option)) =
  match e with
  |  Null _
  |  Var _ | SConst _ | CConst _ -> ((Some e), None)
  |  IConst (v, l) ->
    if v >= 0 then
      ((Some e), None)
    else
      (* if v < 0 then *)
      (None, (Some ( IConst (- v, l))))
  (* else (None, None) *)
  | FConst (v, l) ->
    if v >= 0.0 then
      ((Some e), None)
    else
      (* if v < 0.0 then *)
      ((None, (Some (FConst (-. v, l)))))
  (* else (None, None) *)
  |  Add (e1, e2, l) ->
    let (ts1, tm1) = split_sums e1 in
    let (ts2, tm2) = split_sums e2 in
    let tsr =
      (match (ts1, ts2) with
       | (None, None) -> None
       | (None, Some r1) -> ts2
       | (Some r1, None) -> ts1
       | (Some r1, Some r2) -> Some ( Add (r1, r2, l))) in
    let tmr =
      (match (tm1, tm2) with
       | (None, None) -> None
       | (None, Some r1) -> tm2
       | (Some r1, None) -> tm1
       | (Some r1, Some r2) -> Some ( Add (r1, r2, l)))
    in (tsr, tmr)
  |  Subtract (e1, e2, l) ->
    Error.report_error
      {
        Error.error_loc = l;
        Error.error_text =
          "got subtraction !! (Should have already been simplified )";
      }
  | Mult (e1, e2, l) ->
    let ts1, tm1 = split_sums e1 in
    let ts2, tm2 = split_sums e2 in
    let r =
      match ts1, tm1, ts2, tm2 with
      | None, None, _, _ -> None, None
      | _, _, None, None -> None, None
      | Some r1, None, Some r2, None -> Some (Mult (r1, r2, l)), None
      | Some r1, None, None, Some r2 -> None, Some (Mult (r1, r2, l))
      | None, Some r1, Some r2, None -> None, Some (Mult (r1, r2, l))
      | None, Some r1, None, Some r2 -> Some (Mult (r1, r2, l)), None
      | _ -> ((Some e), None) (* Undecidable cases *)
    in r
  | Div (e1, e2, l) ->
        let ts1, tm1 = split_sums e1 in
        let ts2, tm2 = split_sums e2 in
        let r =
          match ts1, tm1, ts2, tm2 with
            | None, None, _, _ -> None, None
            | _, _, None, None -> failwith "[cpure.ml] split_sums: divide by zero"
            | Some r1, None, Some r2, None -> Some (Div (r1, r2, l)), None
            | Some r1, None, None, Some r2 -> None, Some (Div (r1, r2, l))
            | None, Some r1, Some r2, None -> None, Some (Div (r1, r2, l))
            | None, Some r1, None, Some r2 -> Some (Div (r1, r2, l)), None
            | _ -> Some e, None
        in r
  |  Max (e1, e2, l) ->
         Error.report_error
             {
                 Error.error_loc = l;
                 Error.error_text =
                     "got Max !! (Should have already been simplified )";
             }
  |  Min (e1, e2, l) ->
         Error.report_error
             {
                 Error.error_loc = l;
                 Error.error_text =
                     "got Min !! (Should have already been simplified )";
             }
  |  TypeCast _ -> ((Some e), None)
  |  Bag (e1, l) -> ((Some e), None)
  |  BagUnion (e1, l) -> ((Some e), None)
  |  BagIntersect (e1, l) -> ((Some e), None)
  |  BagDiff (e1, e2, l) -> ((Some e), None)
  |  ArrayAt _ -> ((Some e), None)
  | Concat (e1, e2, l) -> ((Some e), None)


(*
   lhs-lsm = rhs-rsm   ==> lhs+rsm = rhs+lsm
*)
and move_lr (lhs :  exp option) (lsm :  exp option)
    (rhs :  exp option) (rsm :  exp option) l :
  ( exp *  exp) =
  let nl =
    match (lhs, rsm) with
    | (None, None) ->  IConst (0, l)
    | (Some e, None) -> e
    | (None, Some e) -> e
    | (Some e1, Some e2) ->  Add (e1, e2, l) in
  let nr =
    match (rhs, lsm) with
    | (None, None) ->  IConst (0, l)
    | (Some e, None) -> e
    | (None, Some e) -> e
    | (Some e1, Some e2) ->  Add (e1, e2, l)
  in (nl, nr)

(*
   lhs-lsm = max(rhs-rsm,qhs-qsm)
   ==> lhs+rsm+qsm = max(rhs+lsm+qsm,qhs+lsm+rsm)
*)
and move_lr3 (lhs :  exp option) (lsm :  exp option)
    (rhs :  exp option) (rsm :  exp option) (qhs :  exp option) (qsm :  exp option) loc :
  ( exp *  exp * exp) =
  let rec add e ls = match e,ls with
    | None,[] -> IConst (0, loc)
    | Some e,[] -> e
    | None,l::ls ->  add (Some l) ls
    | Some e,l::ls ->  add (Some (Add (e,l,loc))) ls in
  let rl,ql = match lsm with
    | None -> [],[]
    | Some e -> [e],[e] in
  let ll,ql = match rsm with
    | None -> [],ql
    | Some e -> [e],e::ql in
  let ll,rl = match qsm with
    | None -> ll,rl
    | Some e -> e::ll,e::rl in
  (add lhs ll, add rhs rl, add qhs ql)

and purge_mult (e: exp) : exp =
  (* let pr = string_of in *)
  (* Debug.no_1 "purge_mult" pr pr *) purge_mult_x e

and purge_mult_x (e :  exp):  exp = match e with
  |  Null _ |  Var _ |  IConst _ | FConst _ | SConst _ | CConst _ -> e
  |  Add (e1, e2, l) ->  Add ((purge_mult e1), (purge_mult e2), l)
  |  Subtract (e1, e2, l) ->  Subtract((purge_mult e1), (purge_mult e2), l)
  | Mult (e1, e2, l) ->
        let t1 = purge_mult e1 in
        let t2 = purge_mult e2 in
        begin
          match t1 with
            | IConst (v1, _) ->
                  if (v1 = 0) then t1
                  else if (v1 = 1) then t2
                  else begin
                    match t2 with
                      | IConst (v2, _) -> IConst (v1 * v2, l)
                      | FConst (v2, _) -> FConst ((float_of_int v1) *. v2, l)
                      | _ -> if (v1=2) then Add(t2,t2,l)
                        else Mult (t1, t2, l)
                  end
            | FConst (v1, _) ->
                  if (v1 = 0.0) then t1
                  else begin
                    match t2 with
                      | IConst (v2, _) -> FConst (v1 *. (float_of_int v2), l)
                      | FConst (v2, _) -> FConst (v1 *. v2, l)
                      | _ -> Mult (t1, t2, l)
                  end
            | _ ->
                  begin
                    match t2 with
                      | IConst (v2, _) ->
                            if (v2 = 0) then t2
                            else if (v2 = 1) then t1
                            else if (v2 = 2) then Add(t1,t1,l)
                            else Mult (t1, t2, l)
                      | FConst (v2, _) ->
                            if (v2 = 0.0) then t2
                            else Mult (t1, t2, l)
                      | _ -> Mult (t1, t2, l)
                  end
        end
  | Div (e1, e2, l) ->
        let t1 = purge_mult e1 in
        let t2 = purge_mult e2 in
        Div (t1, t2, l)
  |  Max (e1, e2, l) ->  Max((purge_mult e1), (purge_mult e2), l)
  |  Min (e1, e2, l) ->  Min((purge_mult e1), (purge_mult e2), l)
  |  TypeCast (ty, e1, l) -> TypeCast (ty, purge_mult e1, l)
  |  Bag (el, l) ->  Bag ((List.map purge_mult el), l)
  |  BagUnion (el, l) ->  BagUnion ((List.map purge_mult el), l)
  |  BagIntersect (el, l) ->  BagIntersect ((List.map purge_mult el), l)
  |  BagDiff (e1, e2, l) ->  BagDiff ((purge_mult e1), (purge_mult e2), l)
  | ArrayAt (e1, i, p) -> ArrayAt (e1, List.map purge_mult i, p)
  | Concat (e1, e2, l) -> Concat (purge_mult e1, purge_mult e2, l)
