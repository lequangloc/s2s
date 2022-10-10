let source_files = ref ([] : string list)


let parse_arguments = [
    ("-sat", Arg.Set Smtlib_translate.is_sat, "translate sat problem");
    ("-en-xp", Arg.Set Smtlib_translate.b_include_expect, "include expected output");

]

let usage_msg = (Sys.argv.(0) ^" [options] \n")

let set_source_file arg =
  source_files := arg :: !source_files


let process_cmd_line () =
  Arg.parse parse_arguments set_source_file usage_msg
