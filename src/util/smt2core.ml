open Globals
open Gen
open Smtlib_syntax
open Smtlib_util

open VarGen
open Cpure
open Exp
open Var

let trans_symbol sym=
  match sym with
    | Symbol (_, s) -> s
    | SymbolWithOr (_, s) -> s

let trans_identifier ident=
  match ident with
    | IdSymbol (_, s1) -> s1
    | IdUnderscoreSymNum _ -> failwith "smt2core.trans_var.match_sort: not supported 1"

let trans_qualidentifier qID= match qID with
  | QualIdentifierId (_, tid) -> tid
  | QualIdentifierAs _ -> failwith "smt2core.trans_formula.match_term: not support yet 2"

let trans_sort so=
  let t = match so with
    | SortIdentifier (_, t) -> begin
        let tsymbol = trans_identifier t in
        let t = trans_symbol tsymbol in
        match t with
          | "String" -> String
          | "Int" -> Int
          | _ -> failwith ("smt2core.trans_var.match_sort: not supported type " ^ t)
      end
    | SortIdSortMulti _ -> failwith "smt2core.trans_var.match_sort: not support yet 2"
  in
  t

let trans_var (p, s, so) =
  let id = match s with
    | Symbol (_, id)
    | SymbolWithOr (_, id) -> id
  in
  let t = trans_sort so (*  match so with *)
    (* | SortIdentifier (_, t) -> begin *)
    (*     let tsymbol = trans_identifier t in *)
    (*     let t = trans_symbol tsymbol in *)
    (*     match t with *)
    (*       | "String" -> String *)
    (*       | "Int" -> Int *)
    (*       | _ -> failwith ("smt2core.trans_var.match_sort: not supported type " ^ t) *)
    (*   end *)
    (* | SortIdSortMulti _ -> failwith "smt2core.trans_var.match_sort: not support yet 2" *)
  in
  mk_unprimed t id


let trans_vars = List.map trans_var

let trans_quan_var sortedvar =
  match sortedvar with
    | SortedVarSymSort (_, sym, so) ->
          let id = trans_symbol sym in
          let t = trans_sort so in
          mk_unprimed t id
    (* | _ -> failwith "smt2core.trans_quan_var: not happen 1" *)

let trans_quan_vars vl=
  List.map trans_quan_var vl

let from_string_to_chars s p=
  let l = (String.length s) -2 in (*not cout " "*)
  let rec helper i res=
    if i > l then res else 
      let new_res = Concat (res, CConst (Char.code (s.[i]) , p), p) in
      helper (i + 1) new_res
  in
  if l = 0 then failwith "smt2core: from_string_to_chars " (* CConst (Char.code ('') , p) *)
  else
    let () = Debug.ninfo_hprint (add_str  "s " pr_id) s no_pos in
    let () = Debug.ninfo_hprint (add_str  "length " string_of_int) l no_pos in
    helper 2 (CConst (Char.code s.[1], p))

let trans_exp vars e=
  match e with
    | SpecConstsDec (_, s) -> failwith "smt2core.trans_exp.match_specconstant1: not support yet 1"
    | SpecConstNum ((p, _), s) -> IConst (int_of_string s, (pos_w_line p))
    | SpecConstString ((p, _), s) -> begin
        (*look up in vars*)
        try
          let var = List.find (fun sv -> string_cmp sv.id s =0) vars in
          Var (var,  (pos_w_line p))
        with Not_found ->
            let () = Debug.ninfo_hprint (add_str  "SConst " string_of_int) 1 no_pos in
            (* SConst (s,  (pos_w_line p)) *)
            from_string_to_chars s (pos_w_line p)
      end
    | _ -> failwith "smt2core.trans_formula.match_specconstant1: not support yet 4"


let rec trans_term_exp vars t=
  match t with
    | TermSpecConst (_ , specconstant1) -> begin
        trans_exp vars specconstant1
      end
    | TermQualIdentifier ((p, _), qualidentifier1) -> begin
          let sym = trans_qualidentifier qualidentifier1 in
          let id = trans_symbol (trans_identifier sym) in
          (*look up in vars*)
          try
            let var = List.find (fun sv -> string_cmp sv.id id =0) vars in
            Var (var,  (pos_w_line p))
          with Not_found -> SConst (id,  (pos_w_line p))
      end
    | TermQualIdTerm ((p,_), qualID, (_, terms)) -> begin
        let ident = trans_qualidentifier qualID in
        let tt = trans_symbol (trans_identifier ident) in
        (* let () = print_endline ("smt2core.TermQualIdTerm: tt = " ^ tt) in *)
        let exps = List.map (trans_term_exp vars) terms in
        match tt with
          | "Concat" -> begin
              match exps with
                | [e1;e2] -> Concat (e1, e2,  (pos_w_line p))
                | _ -> failwith "smt2core.trans_term_exp.match_tt: 3a"
            end
          | "Length" -> begin
              match exps with
                | [e1] -> begin
                    match e1 with
                      | Var (sv, p) -> begin
                          let id = Globals.lookup_sleng_insert  sv.Var.id in
                          let isv = {Var.t = Int; Var.id = id;
                          Var.p = sv.Var.p;
                          } in
                          Var (isv, p)
                        end
                      | _ -> failwith "smt2core.trans_term_exp.match_tt: 4a"
                  end
                | _ -> failwith "smt2core.trans_term_exp.match_tt: 4"
            end
          | "+" ->  begin
              match exps with
                | [e1;e2] -> Add (e1, e2,  (pos_w_line p))
                | _ -> failwith "smt2core.trans_term_exp.match_tt: 3b"
            end
          | "-" ->  begin
              match exps with
                | [e1;e2] -> Subtract (e1, e2,  (pos_w_line p))
                | _ -> failwith "smt2core.trans_term_exp.match_tt: 3b"
            end
          | "*" ->  begin
              match exps with
                | [e1;e2] -> Mult (e1, e2,  (pos_w_line p))
                | _ -> failwith "smt2core.trans_term_exp.match_tt: 3b"
            end
          | _ -> failwith "smt2core.trans_term_exp.match_tt: not support yet 2"
      end
    | _ -> failwith "smt2core.trans_term_exp.match_t: not support yet 5"

let rec trans_formula vars (p, t)=
  match t with
    | TermSpecConst (_ , specconstant1) -> begin
        failwith "smt2core.trans_formula.match_term: TermSpecConst is an exp "
      end
    | TermQualIdentifier _ -> failwith "smt2core.trans_formula.match_term: TermQualIdentifier is an exp "
    | TermQualIdTerm ((p, _), qualID, (_, terms)) -> begin
        let ident = trans_qualidentifier qualID in
        let tt = trans_symbol (trans_identifier ident) in
        let exps = List.map (trans_term_exp vars) terms in
        match tt with
          | "=" -> begin
              match exps with
                | [e1;e2] -> BForm  (Term.Eq (e1, e2,  (pos_w_line p)))
                | _ -> failwith "smt2core.trans_formula.match_tt: 3"
            end
          | ">=" ->  begin
              match exps with
                | [e1;e2] -> BForm  (Term.Gte (e1, e2,  (pos_w_line p)))
                | _ -> failwith "smt2core.trans_formula.match_tt: 3"
            end
          | ">" ->  begin
              match exps with
                | [e1;e2] -> BForm  (Term.Gt (e1, e2,  (pos_w_line p)))
                | _ -> failwith "smt2core.trans_formula.match_tt: 3"
            end
          | "<=" ->  begin
              match exps with
                | [e1;e2] -> BForm  (Term.Lte (e1, e2,  (pos_w_line p)))
                | _ -> failwith "smt2core.trans_formula.match_tt: 3"
            end
          | "<" ->  begin
              match exps with
                | [e1;e2] -> BForm  (Term.Lt (e1, e2,  (pos_w_line p)))
                | _ -> failwith "smt2core.trans_formula.match_tt: 3"
            end
          | _ -> failwith "smt2core.trans_formula.match_tt: not support yet 2"
      end
    | TermExistsTerm (((p, _) as pd),  (_, vl), t) ->
          let s1 = trans_quan_vars vl in
          let new_vars = s1@vars in
          let p = trans_formula new_vars (pd,t) in
          add_quantifiers s1 p
    | _ -> failwith "smt2core.trans_formula.match_term: not support yet 1"


and trans_formulas vars = List.map (trans_formula vars)
