open VarGen
open Globals
open Printf
open Gen.Basic
open Gen.BList

open Iheap
open Ipure
open Iterm
open Iexp

module IH = Iheap
module Ihn = IheapNode

type var_info = { mutable sv_info_kind : typ; id: int; }

type var_type_list = (( ident * var_info)  list)

let type_list_add v en (tlist:var_type_list) =
  let  n_tl = List.remove_assoc v tlist in
  (v,en)::n_tl

let string_of_tlist (tlist:var_type_list) =
  let rec aux t_l = (
    match t_l with
    | [] -> ""
    | (ident, sv_info)::tl ->
          let str_hd = "(" ^ ident ^ ":" ^ (string_of_int sv_info.id)
            ^ ":"^ (string_of_typ sv_info.sv_info_kind) ^ ")" in
          str_hd ^ (aux tl)
  ) in
  "["^(aux tlist)^"]"

let string_of_tlist_type (tl,t)=
  (string_of_tlist tl)^", "^(string_of_typ t)

let string_of_tlist_type_option (tl,t) =
  (string_of_tlist tl)^", "^(pr_option string_of_typ t)

let get_type tlist i =
  let key = "TVar__"^(string_of_int i) in
  ( try
      let (v,en) = List.find (fun (var,bk) -> var=key) tlist in
      en.sv_info_kind
    with _ -> report_error no_pos ("UNEXPECTED : Type Var "^key^" cannot be found in tlist"))

let get_type_entire tlist t =
  let rec helper t = match t with
    | TVar j -> get_type tlist j
    | _ -> t
  in helper t


let fresh_proc_var_kind tlist et =
  match et with
  | TVar i -> { sv_info_kind = et; id = i}
  | _ -> { sv_info_kind = et; id = fresh_int ()}

let fresh_tvar_rec tlist =
  let i = fresh_int() in
  let key = "TVar__"^(string_of_int i) in
  let t2 = TVar i in
  let en={ sv_info_kind = t2; id = i} in
  (en, (key,en)::tlist)

let fresh_tvar tlist =
  let (en, n_tlist) = fresh_tvar_rec tlist in
  (en.sv_info_kind,n_tlist)

let fresh_int_en en =
  match en with
  | TVar i -> i
  | _ -> fresh_int()

let rec trans_type_back (te : typ) : typ =
  match te with
  | Named n -> Named n
  | Array (t, d) -> Array (trans_type_back t, d)
  | p -> p

and sub_type (t1 : typ) (t2 : typ) =
  try
    let it1 = trans_type_back t1 in
    let it2 = trans_type_back t2 in
    Inode.sub_type it1 it2
  with _ -> false

let rec dim_unify d1 d2 = if (d1 = d2) then Some d1 else None

let rec must_unify_x (k1 : typ) (k2 : typ) tlist pos : (var_type_list * typ) =
  let (n_tlist,k) = unify_type k1 k2 tlist in
  match k with
  | Some r -> (n_tlist,r)
  | None -> let msg = ("UNIFICATION ERROR : at location "^(string_of_full_loc pos)
                       ^" types "^(string_of_typ (get_type_entire tlist k1))
                       ^" and "^(string_of_typ (get_type_entire tlist k2))^" are inconsistent") in
    (* if !Globals.enforce_type_error then report_error pos msg *)
    (* else *) (report_warning pos msg; (n_tlist, UNK))

and must_unify (k1 : typ) (k2 : typ) tlist pos : (var_type_list * typ) =
  let pr = string_of_typ in
  let pr_tl =  string_of_tlist in
  let pr_out = pr_pair pr_tl string_of_typ in
  Debug.no_3 "must_unify" pr pr pr_tl pr_out
      (fun _ _ _ -> must_unify_x k1 k2 tlist pos) k1 k2 tlist

and unify_type (k1 : typ) (k2 : typ)  tlist : (var_type_list * (typ option)) =
  let pr = string_of_typ in
  let pr2 = pr_pair string_of_tlist (pr_option pr) in
  Debug.no_2 "unify_type" pr pr pr2 (fun _ _ -> unify_type_x k1 k2 tlist) k1 k2

and unify_type_x (k1 : typ) (k2 : typ) tlist : (var_type_list * (typ option)) =
  unify_type_modify true k1 k2 tlist

and unify_type_modify (modify_flag: bool) (k1 : typ) (k2 : typ) tlist : (var_type_list*(typ option)) =
  let rec repl_tlist i k tl = repl_tvar_in unify modify_flag tl i k
  and unify k1 k2 tl =
    match k1,k2 with
    | UNK, _ -> (tl,Some k2)
    | _, UNK -> (tl,Some k1)
    | Int, NUM -> (tl,Some Int) (* HACK here : give refined type *)
    | Float, NUM -> (tl,Some Float) (* give refined type *)
    | NUM, Int -> (tl,Some Int)
    | NUM, Float -> (tl,Some Float)
    | Int, Float -> (tl,Some Float)
    | Float, Int -> (tl,Some Float)
    | Named n1, Named n2 when (String.compare n1 "memLoc" = 0) || n1="" ->   (* k1 is primitive memory predicate *)
      (tl, Some (Named n2))
    | Named n1, Named n2 when (String.compare n2 "memLoc" = 0) || n2=""  ->   (* k2 is primitive memory predicate *)
      (tl, Some (Named n1))
    | t1, t2  -> (
        let () = Debug.ninfo_hprint (add_str  "t1 " (string_of_typ)) t1 no_pos in
        let () = Debug.ninfo_hprint (add_str  "t2 " (string_of_typ)) t2 no_pos in
        if is_null_type t1 then (tlist, Some k2)
        else if is_null_type t2 then (tlist, Some k1)
        else
        if sub_type t1 t2 then (tlist, Some k2)  (* found t1, but expecting t2 *)
        else if sub_type t2 t1 then (tlist,Some k1)
        else
          begin
            match t1,t2 with
            | TVar i1,_ -> repl_tlist i1 k2 tl
            | _,TVar i2 -> repl_tlist i2 k1 tl
            | BagT x1,BagT x2 ->
              (match (unify x1 x2 tl) with
               | (n_tl,Some t) -> (n_tl,Some (BagT t))
               | (n_tl,None) -> (n_tl,None))
            | Array (x1,d1),Array (x2,d2) ->
              (match (dim_unify d1 d2), (unify x1 x2 tl) with
               | Some d, (n_tl,Some t)  -> (n_tl,Some (Array (t,d)))
               | _,(n_tl,_) -> (n_tl,None))
            | _,_ -> (tl,None)
          end
      )
  in unify k1 k2 tlist

and unify_expect_modify (modify_flag:bool) (k1 : typ) (k2 : typ) tlist : (var_type_list*(typ option)) =
  let bal_unify k1 k2 tl= unify_type_modify modify_flag k1 k2 tl in
  let repl_tlist i k tl = repl_tvar_in bal_unify modify_flag tl i k in
  let rec unify k1 k2 tl =
    match k1,k2 with
    | UNK, _ -> (tl ,Some k2)
    | _, UNK -> (tl,Some k1)
    | Int, NUM -> (tl,Some Int) (* give refined type *)
    | Float, NUM -> (tl,Some Float) (* give refined type *)
    | Int , Float -> (tl,Some Float) (*LDK*)
    | Float , Int -> (tl,Some Float) (*LDK*)
    | t1, t2  ->
      if sub_type t1 t2 then (tl,Some k2)  (* found t1, but expecting t2 *)
      (* else if sub_type t2 t1 then Some k1 *)
      else
        begin
          match t1,t2 with
          | TVar i1,_ -> repl_tlist i1 k2 tl
          | _,TVar i2 -> repl_tlist i2 k1 tl
          | BagT x1,BagT x2 -> (
              match (unify x1 x2 tl) with
              | (n_tl,Some t) -> (n_tl,Some (BagT t))
              | (n_tl,None) -> (n_tl,None)
            )
          | Array (x1,d1),Array (x2,d2) -> (
              match (dim_unify d1 d2), (unify x1 x2 tl) with
              | Some d, (n_tl,Some t)  -> (n_tl,Some (Array (t,d)))
              | _,(n_tl,_)-> (n_tl,None)
            )
          | _,_ -> (tlist,None)
        end
  in unify k1 k2 tlist

and repl_tvar_in unify flag tlist i k =
  let test x = (
    let i2 = x.id in
    match k with
    | TVar j -> i2=i || i2=j
    | _ -> i2=i
  ) in
  let new_k = (
    match k with
    | TVar _ -> UNK
    | _ -> k
  ) in
  let res_t = List.fold_right (fun (v,en) (_tl,et) ->
      match et with
      | None -> (_tl,et)
      | Some t1 ->
        if not(test en) then (_tl,et)
        else
          match en.sv_info_kind with
          | TVar _ -> (_tl,et)
          | t -> (unify t t1 _tl)
    ) tlist (tlist, Some new_k) in
  match res_t with
  | (n_tl,None) -> (n_tl,None)
  | (n_tl,Some ut) ->
    let ut = match ut with
      | UNK -> k 
      | _ -> ut in
    (* TVar i --> ut *)
    if flag then (
      let rec aux t_l = (
        match t_l with 
        | [] -> []
        | (v,en)::tail ->
          if test en then 
            let n_en = { sv_info_kind = ut; id = en.id} in
            let n_el = (v,n_en) in
            n_el::(aux tail)
          else 
            let nt = subs_tvar_in_typ en.sv_info_kind i ut in
            let n_en = { sv_info_kind = nt; id = en.id} in
            let n_el = (v,n_en) in
            n_el::(aux tail) 
      ) in
      let n_tlist = aux n_tl in
      (n_tlist,Some ut)
    ) else (n_tl,Some ut) 

let rec must_unify_expect_x (k1 : typ) (k2 : typ) tlist pos : (var_type_list * typ) =
  let (n_tl,k) = unify_expect k1 k2 tlist in
  match k with
  | Some r -> (n_tl,r)
  | None -> report_error pos ("TYPE ERROR 1 : Found "
                              ^(string_of_typ (get_type_entire tlist k1))
                              ^" but expecting "^(string_of_typ (get_type_entire  tlist k2)))

and must_unify_expect (k1 : typ) (k2 : typ) tlist pos : (var_type_list * typ)  =
  Debug.no_3 "must_unify_expect" string_of_typ string_of_typ string_of_tlist string_of_tlist_type (fun _ _ _ -> must_unify_expect_x k1 k2 tlist pos) k1 k2 tlist


and unify_expect (k1 : typ) (k2 : typ) tlist : (var_type_list*(typ option)) =
  unify_expect_modify true k1 k2 tlist

let must_unify_expect_test k1 k2 tlist pos =
  let (_,k) = unify_expect_modify false k1 k2 tlist  in
  match k with
  | Some r -> r
  | None -> Gen.report_error pos ("TYPE ERROR 2 : Found "
    ^(string_of_typ (k1))
    ^" but expecting "^(string_of_typ (k2)))

let unify_ptr_arithmetic_x (t1,new_et) (t2,new_et2) et n_tl2 pos =
  if is_possible_node_typ t1 && !Globals.b_pointer_arith then
    let (n_tl2,_) = must_unify_expect t1 et n_tl2 pos in
    let (n_tlist2,_) = must_unify_expect t2 NUM n_tl2 pos in
    (n_tlist2,t1)
  else if is_possible_node_typ t2 && !Globals.b_pointer_arith then
    let (n_tl2,_) = must_unify_expect t2 et n_tl2 pos in
    let (n_tlist2,_) = must_unify_expect t1 NUM n_tl2 pos in
    (n_tlist2,t2)
  else
    let (n_tlist1,t1) = must_unify_expect t1 et n_tl2 pos in
    let (n_tlist2,t2) = must_unify_expect t2 et n_tlist1 pos in
    let (n_tlist2,t2) = must_unify t1 t2 n_tlist2 pos in
    (n_tlist2,t2)

let unify_ptr_arithmetic (t1,new_et) (t2,new_et2) et n_tl2 pos =
  let pr_t = string_of_typ in
  Debug.no_4 "unify_ptr_arithmetic" pr_t pr_t pr_t string_of_tlist (pr_pair string_of_tlist string_of_typ)
      (fun _ _ _ _ -> unify_ptr_arithmetic_x (t1,new_et) (t2,new_et2) et n_tl2 pos) t1 t2 et n_tl2

let gather_type_info_var_x (var : ident) tlist (ex_t : typ) pos : (var_type_list * typ) =
  if (is_dont_care_var var) then
    (tlist, UNK) (* for vars such as _ and # *)
  else
    try
      let (ident, k) = List.find (fun (a,b) -> a = var )tlist in
      let (n_tlist,tmp) = must_unify k.sv_info_kind ex_t tlist pos in
      let n_tlist = type_list_add ident {sv_info_kind = tmp;id=k.id} n_tlist in
      (n_tlist, tmp )
    with
      | Not_found ->
            let vk = fresh_proc_var_kind tlist ex_t in
            ((var,vk)::tlist, vk.sv_info_kind)
      | ex ->
            let _ = print_string_quiet (get_backtrace_quiet ()) in
            report_error pos ("gather_type_info_var : unexpected exception "^(Printexc.to_string ex))

let gather_type_info_var (var : ident) tlist (ex_t : typ) pos :
      (var_type_list*typ) =
  let pr = string_of_typ in
  Debug.no_3 "gather_type_info_var" (fun x -> ("ident: "^x))
      string_of_tlist pr string_of_tlist_type 
    (fun _ _ _ -> gather_type_info_var_x var tlist ex_t pos) var tlist ex_t

let rec gather_type_info_exp_x a0 tlist et = match a0 with
  | Null pos ->
        let (new_et,n_tl) = fresh_tvar tlist in
        (n_tl, new_et)
  | Ann_Exp (e,t, _) ->
        let (n_tl,n_typ) = gather_type_info_exp_x e tlist t in
        (n_tl,n_typ)
  | Var ((sv, sp), pos) ->
        let (n_tl,n_typ) =  gather_type_info_var sv tlist et pos in
        (n_tl,n_typ)
  | IConst (_,pos) ->
        let t = int_type in
        let (n_tl,n_typ) = must_unify_expect t et tlist pos in
        (n_tl,n_typ)
  | FConst (_,pos) ->
        let t = float_type in
        let (n_tl,n_typ) = must_unify_expect t et tlist pos in
        (n_tl,n_typ)
  | SConst (_,pos) | CConst (_,pos) ->
        let t = string_type in
        let (n_tl,n_typ) = must_unify_expect t et tlist pos in
        (n_tl,n_typ)
  | Add (a1, a2, pos) ->
        let (new_et, n_tl) =
          if !Globals.b_pointer_arith then (UNK,tlist)
          else fresh_tvar tlist in
        let tmp1 = try
          fst(List.find (fun (v,en) ->
              en.sv_info_kind = new_et) n_tl)
        with _ -> "" in
        let () = Debug.ninfo_hprint (add_str "add(et)" string_of_typ) et no_pos in
        let () = Debug.ninfo_hprint (add_str "add(new_et)" string_of_typ) new_et no_pos in
        let (n_tl1,t1) = gather_type_info_exp a1 n_tl new_et in
        let () = Debug.ninfo_hprint (add_str "a1" string_of) a1 no_pos in
        let () = Debug.ninfo_hprint (add_str "t1" string_of_typ) t1 no_pos in
        let new_et2 = if is_node_typ t1 && !Globals.b_pointer_arith
        then Int else new_et in
        let (n_tl2,t2) = gather_type_info_exp a2 n_tl1 new_et2 in
        let () = Debug.ninfo_hprint (add_str "a1" string_of) a2 no_pos in
        let () = Debug.ninfo_hprint (add_str "t2" string_of_typ) t2 no_pos in
        let (n_tlist2,t2) = unify_ptr_arithmetic (t1,new_et) (t2,new_et2) et n_tl2 pos in
        (n_tlist2,t2)
  | Subtract (a1, a2, pos) | Max (a1, a2, pos)
  | Min (a1, a2, pos) | Concat (a1, a2, pos)
  | Mult (a1, a2, pos) | Div (a1, a2, pos) ->
        let todo_unk:Globals.typ = must_unify_expect_test et NUM tlist pos in
        let (new_et, n_tl) = fresh_tvar tlist in
        let (tmp1,tmp2) = List.find (fun (v,en) ->
            en.sv_info_kind = new_et) n_tl in
        let (n_tl1,t1) = gather_type_info_exp a1 n_tl new_et in
        let (n_tl2,t2) = gather_type_info_exp a2 n_tl1 new_et in
        let (n_tlist1,t1) = must_unify_expect t1 et n_tl2 pos in
        let (n_tlist2,t2) = must_unify_expect t2 t1 n_tlist1 pos in
        let n_tl = List.filter (fun (v,en) -> v<>tmp1) n_tlist2 in
        (n_tl,t2)
  | TypeCast (ty, a1, pos) ->
        let todo_unk:Globals.typ = must_unify_expect_test et ty tlist pos in
        let (new_et, n_tl) = fresh_tvar tlist in
        let (tmp1,tmp2) = List.find (fun (v,en) ->
            en.sv_info_kind = new_et) n_tl in
        let (n_tl1,t1) = gather_type_info_exp a1 n_tl new_et in
        let (n_tlist1,t1) = must_unify_expect t1 et n_tl1 pos in
        let n_tl = List.filter (fun (v,en) -> v<>tmp1) n_tl1 in
        (n_tl,t1)
  | BagDiff (a1,a2,pos) ->
        let (el_t, n_tl) = fresh_tvar tlist in
        let new_et = must_unify_expect_test (BagT el_t) et n_tl pos in
        let (n_tlist,t1) = gather_type_info_exp a1 tlist new_et in
        let (n_tlist,t2) = gather_type_info_exp a2 n_tlist new_et in
        let (n_tlist,n_typ) = must_unify t1 t2 n_tlist pos in
        (n_tlist,n_typ)
  | BagIntersect (es,pos) | BagUnion (es,pos) ->
        let (el_t,n_tl) = fresh_tvar tlist in
        let new_et = must_unify_expect_test (BagT el_t) et n_tl pos in
        let rec aux es_list type_list =
          match es_list with
            | []->([],type_list)
            | hd::tl ->
                  let (_tlist,_typ) = gather_type_info_exp hd type_list new_et in
                  let (es_type_list,new_type_list) = aux tl _tlist in
                  (_typ::es_type_list, new_type_list)
        in
        let (es_type_list,new_tl) = aux es n_tl in
        List.fold_left (fun (tl,e) a -> must_unify a e tl pos) (new_tl,new_et) es_type_list
  | Bag (es,pos) ->
        let (el_t,n_tl) = fresh_tvar tlist in
        let (n_tlist,t) = List.fold_left (fun (type_list,et) a ->
            gather_type_info_exp a type_list et) (n_tl,el_t) es in
        (n_tlist,BagT t)
  | ArrayAt ((a,p),idx,pos) ->
        let dim = List.length idx in
        let new_et = Array (et, dim) in
        let (n_tl,lt) = gather_type_info_var a tlist new_et pos in
        let rec aux id_list type_list =
          match id_list with
            | [] -> type_list
            | hd::tl ->
                  let (n_tl,n_typ) = gather_type_info_exp hd type_list Int in
                  aux tl n_tl
        in
        let n_tlist = aux idx n_tl in
        (match lt with
          | Array (r,_) -> (n_tlist,r)
          | _ ->  failwith ("gather_type_info_exp: expecting type Array of dimension " ^ (string_of_int dim) ^ " but given " ^ (string_of_typ lt)))

and gather_type_info_exp a0 tlist et =
  Debug.no_3 "gather_type_info_exp"
      Iexp.string_of string_of_tlist string_of_typ
      string_of_tlist_type
      (fun _ _ _ -> gather_type_info_exp_x a0 tlist et) a0 tlist et


let gather_type_info_term irel_decls (pf : Iterm.t) tlist =
  let unify_ptr_cmp t1 t2 n_tl pos =
    if is_node_typ t1 then
      let (n_tlist2,_) = must_unify_expect t2 Int n_tl pos in
      (true,n_tlist2)
    else if is_node_typ t2 then
      let (n_tlist2,_) = must_unify_expect t1 Int n_tl pos in
      (true,n_tlist2)
    else (false,n_tl)
  in
  match pf with
    | BConst _ -> tlist
    | BVar ((bv, bp), pos) ->
          let (n_tlist,n_type) = gather_type_info_var bv tlist
            (bool_type) pos in
          n_tlist
    | Lt (a1, a2, pos) | Lte (a1, a2, pos) | Gt (a1, a2, pos) | Gte (a1, a2, pos) ->
          let (new_et1,n_tl) = fresh_tvar tlist in
          let (new_et2,n_tl) = fresh_tvar n_tl in
          let (n_tl,t1) = gather_type_info_exp a1 n_tl new_et1 in
          let (n_tl,t2) = gather_type_info_exp a2 n_tl new_et2 in
          let (flag,n_tl) = unify_ptr_cmp t1 t2 n_tl pos in
          if flag then n_tl
          else
            let (n_tl,t1) = must_unify_expect t1 NUM n_tl pos in
            let (n_tl,t2) = must_unify_expect t2 NUM n_tl pos in
            let (n_tl,_) = must_unify t1 t2 n_tl pos  in
            (* UNK, Int, Float, TVar *)
            n_tl
    | EqMin (a1, a2, a3, pos) | EqMax (a1, a2, a3, pos) ->
          let (new_et,n_tl) = fresh_tvar tlist in
          let (n_tl,t1) = gather_type_info_exp a1 n_tl new_et in
          (* tvar, Int, Float *)
          let (n_tl,t2) = gather_type_info_exp a2 n_tl new_et in
          let (n_tl,t3) = gather_type_info_exp a3 n_tl new_et in
          (* tvar, Int, Float *)
          let unif_t = NUM in
          let (n_tl,t1) = must_unify_expect t1 unif_t n_tl pos in
          let (n_tl,t2) = must_unify_expect t2 unif_t n_tl pos in
          let (n_tl,t3) = must_unify_expect t3 unif_t n_tl pos in
          let (n_tl,t) = must_unify t1 t2 n_tl pos  in
          (* UNK, Int, Float, TVar *)
          let (n_tl,t) = must_unify t t3 n_tl pos  in
          n_tl
    | BagIn ((v, p), e, pos) | BagNotIn ((v, p), e, pos) ->  (* v in e *)
          let (new_et,n_tl) = fresh_tvar tlist in
          let (n_tl,t1) = gather_type_info_exp e n_tl (BagT new_et) in
          let (n_tl,t2) = gather_type_info_var v n_tl new_et pos in
          let (n_tl,_)= must_unify t1 (BagT t2) n_tl pos in
          n_tl
    | BagSub (e1, e2, pos) ->
          let (new_et,n_tl) = fresh_tvar tlist in
          let (n_tl,t1) = gather_type_info_exp e1 n_tl (BagT new_et) in
          let (n_tl,t2) = gather_type_info_exp e2 n_tl (BagT new_et) in
          let (n_tl,_) = must_unify t1 t2 n_tl pos in
          n_tl
    | Eq (a1, a2, pos) | Neq (a1, a2, pos) -> (
          let (new_et1,n_tl) = fresh_tvar tlist in
          let (n_tl,t1) = gather_type_info_exp a1 n_tl new_et1 in
          let (new_et2,n_tl) = fresh_tvar n_tl in
          let (n_tl,t2) = gather_type_info_exp a2 n_tl new_et2 in
          let () = Debug.ninfo_hprint (add_str "Eq:t1" string_of_typ) t1 no_pos in
          let () = Debug.ninfo_hprint (add_str "Eq:t2" string_of_typ) t2 no_pos in
          let (n_tl,_) = must_unify t1 t2 n_tl pos  in
          let () = Debug.ninfo_hprint (add_str "Eq:ntl" string_of_tlist) n_tl no_pos in
          n_tl
      )
    | BagMax ((v1, p1), (v2, p2), pos)
    | BagMin ((v1, p1), (v2, p2), pos) -> (* V1=BagMin(V2) *)
          let (et,n_tl) = fresh_tvar tlist in
          let (n_tl,t1) = gather_type_info_var v1 n_tl et pos in
          let (n_tl,t) = must_unify t1 NUM n_tl pos  in
          let (n_tl,_) = gather_type_info_var v2 n_tl (BagT t) pos in
          n_tl
    | RelForm (r, args, pos) -> (
          let helper rdef =
            let args_ctypes = List.map (fun (t,n) -> t ) rdef.Irel.rel_typed_vars in
            let args_exp_types = List.map (fun t -> (t)) args_ctypes in
            let (n_tl,n_typ) = gather_type_info_var r tlist (RelT []) pos in
            let tmp_list = List.combine args args_exp_types in
            let n_tlist = List.fold_left (fun tl (arg,et) ->
                fst (gather_type_info_exp arg tl et )) n_tl tmp_list in
            n_tlist
          in
          try
            let rdef = List.find (fun rdef -> Ustr.str_eq rdef.Irel.rel_name r) irel_decls in
            helper rdef
          with
            | Not_found ->    failwith ("gather_type_info_b_formula: relation " ^ r ^ " cannot be found")
            | Invalid_argument _ -> failwith ("number of arguments for relation " ^ r ^ " does not match")
            | e -> raise e;
      )

let rec gather_type_info_pure_x irel_decls (p0 : Ipure.t) (tlist : var_type_list) : var_type_list =
  match p0 with
    | BForm t -> gather_type_info_term irel_decls t tlist
    | And (p1, p2, pos) | Or (p1, p2, pos) ->
          let n_tl = gather_type_info_pure irel_decls p1 tlist in
          let n_tl = gather_type_info_pure irel_decls p2 n_tl in
          n_tl
    | Not (p1, pos) ->
          let n_tl = gather_type_info_pure_x irel_decls p1 tlist in
          n_tl
    | Forall ((qv, qp), qf, pos) | Exists ((qv, qp), qf, pos) ->
          if (List.exists (fun (v,en)-> v=qv) tlist) then
            Error.report_error {
                Error.error_loc = pos;
                Error.error_text = qv ^ " shadows outer name";
            }
          else
            let (new_et,n_tl) = fresh_tvar tlist in
            let vk = fresh_proc_var_kind n_tl new_et in
            let n_tlist = gather_type_info_pure irel_decls qf ((qv,vk)::n_tl) in
            n_tlist

and gather_type_info_pure irel_decls (p0: Ipure.t) (tlist : var_type_list) : var_type_list =
  let pr1 = Ipure.string_of in
  let pr2 = string_of_tlist in
  Debug.no_2 "gather_type_info_pure" pr1 pr2 pr2
  (fun _ _ -> gather_type_info_pure_x irel_decls p0 tlist) p0 tlist


let rec gather_type_info_heap_x ddecls pdecls (h0 : Iheap.t) tlist =
  let generic_ptr_helper v ies n_tl =
    (* Assumptions:
     * (i)  ies to contain a single argument, namely the value of the pointer
     * (ii) the head of the heap node is of form "V[.TypeOfV].FieldAccess"
     *      where [.TypeOfV] is optional type of V. If it is present, it is
     *      the type of V pointer. Otherwise, we try to find this information
     *      based on its fields.
     * (iii) Temporarily assume that only one field; the case of inline fields
     *      will be dealt with later.
     *)
    (* Step 1: Extract the main variable i.e. the root of the pointer *)
    (* let () = print_endline ("[gather_type_info_heap_x] heap pointer = " ^ v) in *)
    let tokens = Str.split (Str.regexp "\\.") v in
    (* let () = print_endline ("[gather_type_info_heap_x] tokens = {" ^ (String.concat "," tokens) ^ "}") in *)
    let rootptr = List.hd tokens in
    (* Step 2: Determine the type of [rootptr] and the field by looking
     * up the current state of tlist & information supplied by the user.
     *)
    let s = List.nth tokens 1 in
    let type_found,type_rootptr = try
      (* looking up in the list of data types *)
      (* Good user provides type for [rootptr] ==> done! *)
      let ddef =List.find (fun ddecl -> Ustr.str_eq ddecl.Inode.data_name s) ddecls in
      (true, Named ddef.Inode.data_name)
    with
      | Not_found -> (false,UNK)
            (* perform type reasoning! *) in
    let type_found,type_rootptr =
      if type_found then (type_found,type_rootptr)
      else try
        (* looking up in collected types table for [rootptr] *)
        let vi = snd (List.find (fun (v,en) -> v = rootptr) n_tl) in
        match vi.sv_info_kind with
          | UNK -> (false,UNK)
          | _ -> (true,vi.sv_info_kind)
                (* type of [rootptr] is known ==> done! *)
      with
        | Not_found -> (false,UNK) in
    let type_found,type_rootptr =
      if type_found then (type_found,type_rootptr)
      else
        (* inferring the type from the name of the field *)
        let dts = Inode.look_up_types_containing_field ddecls s in
        if (List.length dts = 1) then
          (* the field uniquely determines the data type ==> done! *)
          (* let () = print_endline ("[gather_type_info_heap_x] Only type " ^ (List.hd dts) ^ " has field " ^ s) in *)
          (true,Named (List.hd dts))
        else
          (false,UNK) in
      (* Step 3: Collect the remaining type information *)
      if type_found then
        (* Know the type of rootptr ==> Know the type of the field *)
        let n_tl = ([(rootptr, { sv_info_kind = type_rootptr;
        id = 0 })]@n_tl) in
        (* Filter out user type indication, List.tl to remove the root as well *)
        let field_access_seq = List.tl (List.filter (fun x ->
            Inode.is_not_data_type_identifier ddecls x) tokens) in
        (* Get the type of the field which is the type of the pointer *)
        let ptr_type = Inode.get_type_of_field_seq ddecls type_rootptr field_access_seq in
        let (n_tl,_)= gather_type_info_exp (List.hd ies) n_tl ptr_type in n_tl
      else n_tl
        (* End dealing with generic ptr *)
  in
  match h0 with
    | Star (h1, h2, _ ) ->
          let n_tl = gather_type_info_heap_x ddecls pdecls h1 tlist in
          let n_tl = gather_type_info_heap_x ddecls pdecls h2 n_tl in
          n_tl
    | HeapNode2 h2 ->
          let h = IheapNode.node2_to_pto ddecls h2 in
          let fh = IH.PtoNode h in
          let n_tl = gather_type_info_heap_x ddecls pdecls fh tlist in
          n_tl
    | PtoNode { Ihn.heap_node = (v, p);
      Ihn.heap_arguments = ies; (* arguments *)
      Ihn.heap_deref = deref;
      Ihn.heap_name = v_name; (* data name *)
      Ihn.heap_pos = pos } ->
          Debug.ninfo_hprint (add_str "pto" Iheap.string_of) h0 no_pos;
          Debug.ninfo_hprint (add_str "ies" (pr_list Iexp.string_of)) ies no_pos;
          let n_tl =  tlist in
          (*Deal with the generic pointer! *)
          if (v_name = Globals.generic_pointer_type_name) then
            generic_ptr_helper v ies n_tl
          else
            let n_tl = begin try
              let n_tl = try_unify_data_type_args ddecls v_name v deref ies n_tl pos in
              n_tl
            with
              | Not_found ->
                    Gen.report_error pos (v_name ^ " is neither 2 a data nor pred name")
            end
            in n_tl
    | PredNode {
          Ihn.hpred_arguments = ies; (* arguments *)
          Ihn.hpred_deref = deref;
          Ihn.hpred_name = v_name; (* pred name *)
          Ihn.hpred_pos = pos } ->
          let n_tl = try
            let vdef = List.find (fun pdef -> Ustr.str_eq pdef.Ipred.pred_name v_name) pdecls  in
            try_unify_view_type_args v_name vdef deref ies tlist pos
          with
            | Not_found ->
                  Error.report_error {
                      Error.error_loc = pos;
                      Error.error_text = v_name ^ " is neither 2 a data nor pred name";
                  }
          in n_tl
    | HTrue | HFalse | HEmp -> tlist


and gather_type_info_heap ddecls pdecls (h0 : Iheap.t) tlist =
  Debug.no_2 "gather_type_info_heap"
      IH.string_of string_of_tlist string_of_tlist
      (fun _ _ -> gather_type_info_heap_x ddecls pdecls h0 tlist) h0 tlist


and try_unify_data_type_args ddefs c v deref ies tlist pos =
  let rec deref_str_helper n res=
    if n > 0 then deref_str_helper (n-1) (res^ "_star")
    else res
  in
  let pr_args = pr_list Iexp.string_of in
  if (deref = 0) then (
      try begin
          let ddef = List.find (fun ddef -> Ustr.str_eq ddef.Inode.data_name c) ddefs in
      let (n_tl,_) = gather_type_info_var v tlist ((Named c)) pos in
      let fields = Inode.look_up_all_fields ddefs ddef in
      try
        (*fields may contain offset field and not-in-used*)
        let () = Debug.ninfo_hprint (add_str "ies" pr_args) ies no_pos in
        let f tl arg ((ty,_),_)=
          (let (n_tl,_) =  gather_type_info_exp arg tl ty in
          n_tl)
        in (List.fold_left2 f n_tl ies fields)
      with | Invalid_argument _ ->
          Gen.report_error pos ("number of arguments for data " ^ c
          ^ " does not match"^(pr_list (fun c->c)(List.map Iexp.string_of ies)))
      end
      with Not_found -> raise Not_found
  )
  else (
    (* dereference cases *)
      try begin
        let base_ddecl = (
            let dname = (
                match c with
                  | "int" | "float" | "void" | "bool" -> c ^ "_star"
                  | _ -> c
            ) in
            Inode.look_up_data_def ddefs dname
        ) in
        let holder_name = deref_str_helper deref "" in
        let (n_tl,_) = gather_type_info_var v tlist ((Named holder_name)) pos in
        let fields =  Inode.look_up_all_fields ddefs base_ddecl in
        try
          let f tl arg ((ty,_),_)=
            (let (n_tl,_) = gather_type_info_exp arg tl ty in n_tl)
          in (List.fold_left2 f n_tl ies fields)
        with | Invalid_argument _ ->
            Gen.report_error pos  ("number of arguments for data " ^ c
            ^ " does not match"^(pr_list (fun c->c)(List.map Iexp.string_of ies)))
      end
      with Not_found -> raise Not_found
  )

and try_unify_view_type_args c vdef deref ies tlist pos =
  let rec deref_str_helper n res=
    if n > 0 then deref_str_helper (n-1) (res^ "_star")
    else res
  in
  let dname = vdef.Ipred.pred_data_name in
  let n_tl = tlist in
  (* ( *)
  (*   if (Ustr.str_eq dname "") then tlist *)
  (*   else if vdef.Ipred.pred_is_prim then tlist *)
  (*   else *)
  (*     let expect_dname = deref_str_helper deref "" in *)
  (*     let (n_tl,_) = gather_type_info_var v tlist ((Named expect_dname)) pos in *)
  (*     n_tl *)
  (* ) in *)
  let vt = vdef.Ipred.pred_typed_vars in
  let rec helper exps tvars =
    match (exps, tvars) with
      | ([], []) -> []
      | (e :: rest1, t :: rest2) ->
            let tmp = helper rest1 rest2 in
            (match e with
              | Iexp.Var ((v, p), pos) ->
                    let ty = fst t in (ty, v) :: tmp
              | _ -> tmp)
      | _ ->
            Gen.report_error pos ("number of arguments for view " ^
                (c ^ " does not match"))
  in
  let tmp_r = helper ies vt in
  let (vt_u,tmp_r) = List.partition (fun (ty,_) -> ty==UNK) tmp_r in
  if (Gen.is_empty vt_u)
  then
    let n_tl = (List.fold_left (fun tl (t, n) -> fst(gather_type_info_var n tl (t) pos)) n_tl tmp_r) in
    n_tl
  else begin
    (* below seems wrong to unify against previous var names *)
    (try
      let n_tl = (List.fold_left (fun tl (t, n) -> fst (gather_type_info_var n tl (t) pos))n_tl tmp_r) in
      let f tl arg lhs_v =
        (let et = get_var_kind lhs_v tl  in
        let (n_tl,new_t) = gather_type_info_exp arg tl et in
        let (n_tl,typ) = set_var_kind lhs_v new_t n_tl in n_tl )
      in (List.fold_left2 f n_tl ies vdef.Ipred.pred_vars)
    with | Invalid_argument _ ->
        report_error pos ("number of arguments for view " ^ c ^ " does not match")
    )
  end

and get_var_kind (var : ident) (tlist : var_type_list) =
  try
    let r = snd (List.find (fun (v,en) -> v=var) tlist) in
    r.sv_info_kind
  with Not_found -> UNK

and set_var_kind (var : ident) (k : typ) (tlist : var_type_list) =
  try
    let n_tl = (List.filter (fun (v,en)->v<>var) tlist) in
    let r = snd(List.find (fun (v,en)->v=var) tlist) in
    let n_el = (var,{id=r.id; sv_info_kind=k}) in
    (n_el::n_tl, {id=r.id; sv_info_kind=k})
  with Not_found ->
      let n_tl = (var,{ sv_info_kind = k;id = (fresh_int ()) })::tlist in
      let typ = snd(List.find (fun (v,en)->v=var) n_tl) in
      (n_tl,typ)

(* syn type of every variable among disjs
*)
let synchronize_x f tlists=
  let rec find_diff ls res=
    match ls with
      | [] -> res
      | sv::rest -> begin try
          let (id, vinfo) = List.find (fun (id, vinfo) ->
              Ustr.str_eq id sv.Var.id && (vinfo.sv_info_kind != sv.Var.t)
          ) tlists in
          find_diff rest res@[(sv, Var.mk vinfo.sv_info_kind sv.Var.id sv.Var.p)]
        with Not_found -> find_diff rest res
        end
  in
  let svs = Cformula.fv f in
  let sst = find_diff svs [] in
  Cformula.subst sst f

let synchronize f tlists=
  let pr1 = Cformula.string_of in
  let pr2 = string_of_tlist in
  Debug.no_2 "synchronize" pr1 pr2 pr1
      (fun _ _ -> synchronize_x f tlists) f tlists
