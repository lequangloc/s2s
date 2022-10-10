open Globals
open VarGen
open Gen.Basic


let main_str src_files=
  let queries = Pdispatcher.parsing_smt2 src_files in
  if queries== [] then () else
    let r, op = Kengine.check_sat_str queries in
    let () = print_endline_quiet ("\nResult = " ^(Out.string_of r) ^ "\n") in
    ()

let main_sl src_files=
  let k2c_ctrl = new K2core.k2c src_files Pdispatcher.parsing_core in
  let () = k2c_ctrl # do_built_flow_hierachy () in
  let () = k2c_ctrl # do_parse () in
  let () = k2c_ctrl # do_print_k () in
  (* transform into core/sl logic *)
  let () = k2c_ctrl#trans_prog () in
  let () = k2c_ctrl # do_print_core () in
  let () = k2c_ctrl # do_check_sat () in
  let () = k2c_ctrl # do_check_ent () in
  ()

let main () =
  let _ = record_backtrace_quite () in
  let () = Config.process_cmd_line () in
  (* must be after cmd processing *)
  let () = Debug.read_main () in
  (*start z3, omega*)
  (* let () = if !Tpdispatcher.pure_tp == Others.OmegaCalc then Omega.set_omegacalc () *)
  (* else () in *)
  (* Tpdispatcher.start_prover (); *)
  (* temporal. to unify *)
  let () =
    if !Globals.fe == 1 then main_sl !Globals.source_files
    else main_str !Globals.source_files
  in
  Tpdispatcher.stop_prover ();
  let () = if !VarGen.enable_time_stats then
    begin
      let ptime4 = Unix.times () in
      let t4 = ptime4.Unix.tms_utime +. ptime4.Unix.tms_cutime +. ptime4.Unix.tms_stime +. ptime4.Unix.tms_cstime in
      (* Timelog.logtime # dump; *)
      print_string ("\nTotal analysis time: "
      ^ (string_of_float t4) ^ " second(s)\n"
      ^ "\tTime spent in main process: "
      ^ (string_of_float (ptime4.Unix.tms_utime+.ptime4.Unix.tms_stime)) ^ " second(s)\n"
      ^ "\tTime spent in child processes: "
      ^ (string_of_float (ptime4.Unix.tms_cutime +. ptime4.Unix.tms_cstime)) ^ " second(s)\n")
    end
  else ()
  in
  ()

let () = try
  main ()
with _ -> print_endline "\nunknown"
