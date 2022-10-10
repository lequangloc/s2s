
open Globals


(* let parse_sl (input : string) : command =  ParserCmd.parse_sl_int "sleek string" input *)

let parse_cmds (input_file) : Icmd.t list =
  let org_in_chnl = open_in input_file in
  let cmd = Parser_cmd.parse_sl input_file (Stream.of_channel org_in_chnl) in
  close_in org_in_chnl;
  cmd
