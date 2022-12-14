(* auto-generated by gt *)

let print_help () =
  (* print_endline "./compile -sleek <file>.smt2" *)
  print_endline "./compile <file>.sl14"
;;

(* if (Array.length Sys.argv) >= 1 *)
(* then *)
(*   let option = Sys.argv.(1) in *)
(*   let () = if option = "-sat" then *)
(*     Smtlib_translate.is_sat := true *)
(*   else () *)
(*   in *)
    (* let in_file_name = Sys.argv.(2) in *)
  (* let in_file_name = Sys.argv.(1) in *)
let _ =
  let () = Smtlib_config.process_cmd_line () in
  let in_file_name = List.hd !Smtlib_config.source_files in
    if ((String.length in_file_name) >= 5) &&
      (String.sub in_file_name ((String.length in_file_name) - 4) 4) = "sl14" (* "smt2" *)
    then
      let out_file_name = in_file_name ^ ".ss" in
      let in_channel = open_in in_file_name in
      let lexbuf = Lexing.from_channel in_channel in
      let parsed  = Smtlib_parse.main Smtlib_lex.token lexbuf in
      match parsed with
        | None ->
              print_help ()
        | Some(x) ->
              let s = Smtlib_translate.trans x in
              let out_channel = open_out out_file_name in
              let _ = Printf.fprintf out_channel "%s" s in
              let _ = close_in in_channel in
              let _ = close_out out_channel in
              ()
    else
      print_help ()
  (* else *)
  (*   print_help () *)
(* else *)
(*   print_help () *)

