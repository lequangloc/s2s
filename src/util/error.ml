
open VarGen

type error = {
  error_loc : loc;
  error_text : string
}


let get_error_type_str ie=
  match ie with
  | 0 -> "bind failure exception"
  | 1 -> "Proving precond failed"
  | 2 -> "Proving assert/assume failed"
  | _ -> ""



(* report error and don't care about the position *)
let report_error_msg (error_msg: string) =
  print_endline_quiet ("\nERROR MESSAGE: " ^ error_msg);
  failwith error_msg

let report_error e =
  if post_pos#is_avail then
    print_endline_quiet ("\nContext of Verification Failure: " ^ post_pos#string_of);
  if proving_loc#is_avail then
    print_endline_quiet ("\nLast Proving Location: " ^  proving_loc#string_of);
  print_endline_quiet ("\nERROR: at " ^ (string_of_loc e.error_loc)
                   ^ "\nMessage: " ^  e.error_text);
  (* flush stdout; *)
  failwith e.error_text

let report_no_pattern () = report_error {error_loc=no_pos; error_text="Kepler error, unhandled pattern"}

let report_error1 e s=
  print_endline_quiet e.error_text;
  if post_pos#is_avail then
    print_endline_quiet ("\nContext of Verification Failure: " ^ post_pos#string_of);
  if proving_loc#is_avail then
    print_endline_quiet ("\nLast Proving Location: " ^ proving_loc#string_of);
  (* flush stdout; *)
  failwith s

let report_warning e =
  if (!VarGen.suppress_warning_msg) then ()
  else if (not !VarGen.en_warning_msg) then report_error1 e "Warning->ERROR"
  else (
    print_endline_quiet ("\nWARNING: "
                     ^  (string_of_loc e.error_loc) ^ ":"
                     ^ e.error_text);
    (* flush stdout; *)
  )
