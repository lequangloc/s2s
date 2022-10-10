
open Globals
open VarGen
open Gen.Basic

open Cpure

module M = Lexer.Make(Token.Token)


let smt_vars = ref ([]: (Smtlib_util.pd * Smtlib_syntax.symbol * Smtlib_syntax.sort) list)
let smt_asserts = ref ([]: (Smtlib_util.pd * Smtlib_syntax.term) list)


let list_parse (input_file) (* : command list *) =
  let org_in_chnl = open_in input_file in
  let parsed =
    let lexbuf = Lexing.from_channel org_in_chnl in
    Smtlib_parse.main Smtlib_lex.token lexbuf  in
  let () =
    match parsed with
      | None -> ()
      | Some(x) ->
            Smtlib_pp.pp x in
  close_in org_in_chnl;
  (* cmd *)
  let () = smt_vars := !Smtlib_pp.vars in
  let () = smt_asserts := !Smtlib_pp.asserts in
  ()

let parsing_smt2 source_files=
  let () = if !Globals.to_smt2 && not !Globals.to_smt2_trau then
    (* print_endline "(set-logic ALL_SUPPORTED)\n" *)
        print_endline "(set-logic QF_S)\n"
  else () in
  let () = list_parse (List.hd source_files) in
  if !Globals.to_smt2 then []
  else
    let () = print_endline "translating from smt to core" in
    let vars = Smt2core.trans_vars !smt_vars in
    (* let () = List.iter (fun var -> print_endline (Var.string_of var)) vars in *)
    let fs = Smt2core.trans_formulas vars !smt_asserts in
    let () = List.iter (fun f ->
        Debug.ninfo_hprint(Gen.add_str "conj" (Cpure.string_of )) f VarGen.no_pos
    ) fs in
    (fs)

let parse_core_file cmds (source_file : string) =
  try
    Parser.parse_cmds source_file
  with
    | End_of_file -> List.rev cmds
    | M.Loc.Exc_located (l,t)-> (
          print_string_quiet ((Camlp4.PreCast.Loc.to_string l)^"\n error: "
          ^(Printexc.to_string t)^"\n at:"^(get_backtrace_quiet ()));
          raise t
      )

let parsing_core src_file=
  (* parse *)
  let cmds = parse_core_file [] src_file in
  let () = if !VarGen.print_parse then
    List.iter (fun c -> print_endline_quiet (Icmd.string_of c)) cmds
  else ()
  in
  cmds
