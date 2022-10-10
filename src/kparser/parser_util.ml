
open Camlp4

open Globals
open VarGen
open Camlp4
open Gen

module DD=Debug
module IP=Ipure

type file_offset ={
    line_num: int;
    line_start: int;
    byte_num: int;
}

let parser_name = (* ref "unknown" *) ref "default"

let set_parser name =
  parser_name := name

let is_cparser_mode = ref false

let un_option s d = match s with
  | Some v -> v
  | None -> d

let error_on_dups f l p =
  if (Gen.BList.check_dups_eq f l) then
    report_error p ("list contains duplicates") else l


let cparser_base_loc = ref {line_num = 1;
                           line_start = 1;
                           byte_num = 1;}


let get_pos x =
  try
    let sp = Parsing.symbol_start_pos () in
    let ep = Parsing. symbol_end_pos () in
    let mp = Parsing.rhs_start_pos x in
    if (!is_cparser_mode) then (
      let new_sp = {sp with Lexing.pos_lnum = sp.Lexing.pos_lnum + !cparser_base_loc.line_num -1;
                            Lexing.pos_bol = sp.Lexing.pos_bol + !cparser_base_loc.byte_num -1;
                            Lexing.pos_cnum = sp.Lexing.pos_cnum + !cparser_base_loc.byte_num -1;} in
      let new_ep = {ep with Lexing.pos_lnum = ep.Lexing.pos_lnum + !cparser_base_loc.line_num -1;
                            Lexing.pos_bol = ep.Lexing.pos_bol + !cparser_base_loc.byte_num -1;
                            Lexing.pos_cnum = ep.Lexing.pos_cnum + !cparser_base_loc.byte_num -1;} in
      let new_mp = {mp with Lexing.pos_lnum = mp.Lexing.pos_lnum + !cparser_base_loc.line_num -1;
                            Lexing.pos_bol = mp.Lexing.pos_bol + !cparser_base_loc.byte_num -1;
                            Lexing.pos_cnum = mp.Lexing.pos_cnum + !cparser_base_loc.byte_num -1;} in
      { start_pos = new_sp;
        end_pos = new_ep;
        mid_pos = new_mp; }
    )
    else (
      { start_pos = sp;
        end_pos = ep;
        mid_pos = mp; }
    )
  with _ -> 
    { start_pos = Lexing.dummy_pos;
      end_pos = Lexing.dummy_pos;
      mid_pos = Lexing.dummy_pos; }

let get_pos_camlp4 l x =
  let sp = Camlp4.PreCast.Loc.start_pos l in
  let ep = Camlp4.PreCast.Loc.stop_pos l in
  let mp = Camlp4.PreCast.Loc.start_pos (Camlp4.PreCast.Loc.shift x l) in
  if (!is_cparser_mode) then (
    let new_sp = {sp with
        Lexing.pos_lnum = sp.Lexing.pos_lnum + !cparser_base_loc.line_num - 1;
        Lexing.pos_bol = sp.Lexing.pos_bol + !cparser_base_loc.byte_num - 1;
        Lexing.pos_cnum = sp.Lexing.pos_cnum + !cparser_base_loc.byte_num - 1;} in
    let new_ep = {ep with
        Lexing.pos_lnum = ep.Lexing.pos_lnum + !cparser_base_loc.line_num - 1;
        Lexing.pos_bol = ep.Lexing.pos_bol + !cparser_base_loc.byte_num - 1;
        Lexing.pos_cnum = ep.Lexing.pos_cnum + !cparser_base_loc.byte_num - 1;} in
    let new_mp = {mp with
        Lexing.pos_lnum = mp.Lexing.pos_lnum + !cparser_base_loc.line_num - 1;
        Lexing.pos_bol = mp.Lexing.pos_bol + !cparser_base_loc.byte_num - 1;
        Lexing.pos_cnum = mp.Lexing.pos_cnum + !cparser_base_loc.byte_num - 1;} in
    { start_pos = new_sp;
      end_pos = new_ep;
      mid_pos = new_mp; }
  )
  else (
    { start_pos = sp;
      end_pos = ep;
      mid_pos = mp; }
  )


let get_heap_id_info (cid: ident * primed) (heap_id : (ident * int * int * Camlp4.PreCast.Loc.t)) =
  let (base_heap_id, ref_level, deref_level, l) = heap_id in
  let s = ref base_heap_id in
  for i = 1 to ref_level do
    s := !s ^ "_star";
  done;
  if (deref_level == 0) then
    (cid, !s, 0)
  else if ((deref_level > 0) && (!is_cparser_mode)) then
    (* dereference case, used to parse specs in C programs *)
    (cid, !s, deref_level)
  else
    report_error (get_pos_camlp4 l 1) "unexpected heap_id"



(* intermediate representation for pure formulae *)
type pure_double =
  | Pure_f of IP.formula
  | Pure_c of Iexp.t


let apply_cexp_form1 fct form = match form with
  | Pure_c f -> Pure_c (fct f)
  | _ -> report_error (get_pos 1) "with 1 expected cexp, found pure_form"

let apply_pure_form1 fct form = match form with
  | Pure_f f -> Pure_f (fct f)
  | _ -> report_error (get_pos 1) "with 1 expected pure_form, found cexp"

let apply_pure_form2 fct form1 form2 = match (form1,form2) with
  | Pure_f f1 ,Pure_f f2 -> Pure_f (fct f1 f2)
  | Pure_f f1 , Pure_c f2 -> (
        match f2 with
          | Iexp.Var (v,_) -> Pure_f (fct f1 (IP.mkBForm (Iterm.mkBVar v (get_pos 1))))
          | _ -> report_error (get_pos 1) "with 2 expected pure_form, found cexp in var"
    )
  | Pure_c f1, Pure_f f2 -> (
        match f1 with
          | Iexp.Var (v,_) -> Pure_f(fct (IP.mkBForm (Iterm.mkBVar v (get_pos 1))) f2)
          | _ -> report_error (get_pos 1) "with 2 expected pure_form in f1, found cexp"
    )
  | Pure_c f1, Pure_c f2 -> (
        let bsv_f1 = (
            match f1 with
              | Iexp.Var (v,_) -> IP.mkBForm (Iterm.mkBVar v (get_pos 1))
              | Iexp.Ann_Exp (Iexp.Var (v, _), Bool, _) ->
                    IP.mkBForm (Iterm.mkBVar v (get_pos 1))
              | _ -> report_error (get_pos 1) "with 2 expected pure_form in f1, found cexp")
        in
        let bsv_f2 = (
            match f2 with
              | Iexp.Var (v,_) -> IP.mkBForm (Iterm.mkBVar v (get_pos 1))
              | Iexp.Ann_Exp (Iexp.Var (v, _), Bool, _) ->
                    IP.mkBForm (Iterm.mkBVar v (get_pos 1))
              | _ -> report_error (get_pos 1) "with 2 expected pure_form in f2, found cexp"
        ) in
        Pure_f (fct bsv_f1 bsv_f2)
    )
  (* | _ -> report_error (get_pos 1) "with 2 expected cexp, found pure_form" *)

let apply_cexp_form2 fct form1 form2 = match (form1,form2) with
  | Pure_c f1, Pure_c f2
  (* | Pure_c f1, Pure_t (f2, _) *) ->  Pure_c (fct f1 f2)
  | _ -> report_error (get_pos 1) "with 2 expected cexp, found pure_form"

(* let apply_cexp_form2 fct form1 form2 = *)
(*   Debug.no_2 "Parser.apply_cexp_form2: " string_of_pure_double string_of_pure_double *)
(*           (fun _ -> "") (apply_cexp_form2 fct) form1 form2 *)

let cexp_list_to_pure fct ls1 = Pure_f (IP.mkBForm (fct ls1))

let cexp_to_pure1 fct f =
  match f with
  (* | Pure_t (f, _) *)
  | Pure_c f -> Pure_f (IP.mkBForm (fct f))
  | _ -> report_error (get_pos 1) "with 1 convert expected cexp, found pure_form"


let cexp_to_pure2 fct f01 f02 =
  match (f01,f02) with
    | Pure_c f1, Pure_c f2 -> (
          let typ1 = Iexp.typ_of_exp f1 in
          let typ2 = Iexp.typ_of_exp f2 in
          if (typ1 = typ2) || (typ1 == UNK) || (typ2 == UNK) then
            Pure_f (IP.mkBForm (fct f1 f2))
          else
            report_error (get_pos 1) "with 2 convert expected the same cexp types, found different types"
      )
  | Pure_f f1 , Pure_c f2 -> (
      match f1  with
      | IP.BForm pf -> (
          match pf with
          | Iterm.Lt (a1, a2, _)
          | Iterm.Lte (a1, a2, _)
          | Iterm.Gt (a1, a2, _)
          | Iterm.Gte (a1, a2, _)
          | Iterm.Eq (a1, a2, _)
          | Iterm.Neq (a1, a2, _) ->
              let tmp = IP.mkBForm (fct a2 f2) in
              Pure_f (IP.mkAnd f1 tmp (get_pos 2))
          | _ -> report_error (get_pos 1) "error should be an equality exp"
        )
      | _ -> begin
          report_error (get_pos 1) "error should be a binary exp"
        end
    )
  | _ -> report_error (get_pos 1) "with 2 convert expected cexp, found pure_form"

