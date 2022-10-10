open VarGen
open Camlp4.PreCast
open Cpure
open Term
open Exp
open Globals
open Lexing
open Gen
module H = Hashtbl
module TI = Typeinf

(******************************************************************************)

let loc = no_pos

class ['a] type_stack_pr (epr:'a->string) (eq:'a->'a->bool)  =
  object (self)
    inherit ['a] stack_pr "type_stack_pr" epr eq as super
    method get_spec_var_ident var p =
      let same_sv sv =
        match sv.Var.p,p with
        | Primed,Primed
        | Unprimed,Unprimed -> Ustr.str_eq sv.Var.id var
        | _ -> false
      in
      try
        super # find same_sv
      with
        Not_found->
        Var.mk UNK var p
  end

let tlist = new type_stack_pr Var.string_of Var.equal

(******************************************************************************)

let expression = Gram.Entry.mk "expression"

(******************************************************************************)

let get_var var tlist =
  if is_substr "PRI" var
  then
    let var = String.sub var 3 (String.length var - 3) in
    tlist # get_spec_var_ident var Primed
  else tlist # get_spec_var_ident var Unprimed

let add_prefix var prefix = Var.mk var.Var.t (prefix ^ var.Var.id) var.Var.p

let is_node evar = match evar with
  | Var (v, _) -> is_node_typ v.Var.t
  | _ -> false


let get_node evar = match evar with 
  | Var (var, _) -> var.Var.id
        (* if var.Var.id=self then var.Var.id else *)
        (*   String.sub var.Var.id 3 (String.length var.Var.id - 3) *)
  | _ -> Gen.report_error no_pos "Expected a pointer variable"

let is_rec_node var = match var with
  (* | Var (SpecVar (_,id,_), _) -> is_substr "RECNOD" id *)
  | _ -> false

let get_rec_node var = String.sub var.Var.id 6 (String.length var.Var.id - 6)

let is_int c = '0' <= c && c <= '9'

let get_type_list_for_fixcalc_output (f:Cpure.formula) =
  let rec helper_e e =
    match e with
      | Add (e1,e2,loc)
      | Subtract (e1,e2,loc)
      | Mult (e1,e2,loc)
      | Div (e1,e2,loc)->
            (helper_e e1) @ (helper_e e2)
      | Var (sv,_)-> [sv]
      | _ -> []
  in
  let helper_b p =
    match p with
    | BConst _
    | BVar _
    | RelForm _ ->
      []
    | Lt (e1,e2,loc)
    | Lte (e1,e2,loc)
    | Gt (e1,e2,loc)
    | Gte (e1,e2,loc)
    | Eq (e1,e2,loc)
    | Neq (e1,e2,loc) ->
      (helper_e e1) @ (helper_e e2)
    | _ -> []
  in
  let rec helper f =
    match f with
    | BForm b-> helper_b b
    | And (f1,f2)
    | Or (f1,f2)-> (helper f1)@(helper f2)
    | Not (nf)
    | Forall (_,nf)
    | Exists (_,nf)-> helper nf
  in
  helper f
;;

let initialize_tlist f =
  tlist # push_list (get_type_list_for_fixcalc_output f)
;;



let initialize_tlist_from_fpairlist fpairlst =
  tlist # push_list ( List.fold_left (fun r (f1,f2,_) -> r@(get_type_list_for_fixcalc_output f1)@(get_type_list_for_fixcalc_output f2)) []  fpairlst)
;;

(******************************************************************************)

EXTEND Gram
    GLOBAL: expression;
expression:
    [ "expression" NONA
        [ x = LIST1 or_formula -> x ]
    ];

or_formula:
    [ "or_formula" LEFTA
        [ x = SELF; "||"; y = SELF -> mkOr x y loc
        | x = and_formula -> x ]
    ];

and_formula:
    [ "and_formula" LEFTA
        [ x = SELF; "&&"; y = SELF -> mkAnd x y loc
        | x = formula -> x ]
    ];

formula:
    [ "formula" LEFTA
        [ NATIVEINT; "="; exp        -> Cpure.mkTrue loc
          | exp; "="; NATIVEINT        -> Cpure.mkTrue loc
          | NATIVEINT; "<"; exp        -> Cpure.mkTrue loc
          | exp; "<"; NATIVEINT        -> Cpure.mkTrue loc
          | NATIVEINT; ">"; exp        -> Cpure.mkTrue loc
          | exp; ">"; NATIVEINT        -> Cpure.mkTrue loc
          | NATIVEINT; "<="; exp       -> Cpure.mkTrue loc
          | exp; "<="; NATIVEINT       -> Cpure.mkTrue loc
          | NATIVEINT; ">="; exp       -> Cpure.mkTrue loc
          | exp; ">="; NATIVEINT       -> Cpure.mkTrue loc
          | NATIVEINT; "!="; exp       -> Cpure.mkTrue loc
          | exp; "!="; NATIVEINT       -> Cpure.mkTrue loc
          | NATIVEINT; "="; NATIVEINT  -> Cpure.mkTrue loc
          | NATIVEINT; "<"; NATIVEINT  -> Cpure.mkTrue loc
          | NATIVEINT; ">"; NATIVEINT  -> Cpure.mkTrue loc
          | NATIVEINT; "<="; NATIVEINT -> Cpure.mkTrue loc
          | NATIVEINT; ">="; NATIVEINT -> Cpure.mkTrue loc
          | NATIVEINT; "!="; NATIVEINT -> Cpure.mkTrue loc
          | x = INT; "="; y = INT ->
                let tmp =
                  if int_of_string x = int_of_string y
                  then BConst (true,loc)
                  else BConst (false,loc)
                in BForm tmp
          | x = exp; "<"; y = exp ->
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) x no_pos in *)
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) y no_pos in *)
                let tmp = Lt (x, y, loc) in BForm tmp
          | x = exp; ">"; y = exp ->
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) x no_pos in *)
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) y no_pos in *)
                let tmp = Gt (x, y, loc) in BForm tmp
          | x = exp; "<="; y = exp ->
                let tmp = Lte (x, y, loc) in BForm tmp
          | x = exp; ">="; y = exp ->
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) x no_pos in *)
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) y no_pos in *)
                let tmp =
                  if is_node x && is_one y then
                    Neq (x, Null loc, loc)
                  else
                    Gte (x, y, loc)
                in BForm tmp
          | x = exp; "="; y = exp ->
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) x no_pos in *)
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) y no_pos in *)
                let tmp = Eq (x, y, loc) in BForm tmp
          | x = exp; "!="; y = exp ->
                let tmp = Neq (x, y, loc) in
                BForm tmp
        ]
    ];

exp:
    [ "exp" LEFTA
        [ x = SELF; "+"; y = SELF -> Add (x, y, loc)
          | x = SELF; "-"; y = SELF -> Subtract (x, y, loc)
          | x = INT; "*"; y = SELF ->
                let ni=IConst (int_of_string x, loc) 
                in Mult (ni, y, loc)
          | x = specvar             -> Var (x, loc)
          | x = INT                 -> IConst (int_of_string x, loc)
          | NATIVEINT               -> Var (Var.mk (Named "abc") "abc" Unprimed,loc)
        ]
    ];

specvar:
    [ "specvar" NONA
        [ x = LIDENT -> get_var x tlist
          | x = UIDENT ->
                if is_substr "REC" x
                then
                  add_prefix (get_var (String.sub x 3 (String.length x - 3)) tlist) "REC"
                else get_var x tlist
        ]
    ];

END

(******************************************************************************)

let parse_fix s = Gram.parse_string expression (Loc.mk "<string>") s

let parse_fix s =
  Debug.no_1 "parse_fix" pr_id (pr_list Cpure.string_of) parse_fix s


