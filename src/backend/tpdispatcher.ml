
open Globals
open GlobProver
open VarGen
open Gen
open Others

open Cpure

module CP= Cpure

let pure_tp = ref Z3
let sat_subno = ref 0

let prover_arg = ref "z3" (* default prover *)
let user_choice = ref false

let rec check_prover_existence prover_cmd_str =
  match prover_cmd_str with
  | [] -> ()
  | "log"::rest -> check_prover_existence rest
  | prover::rest ->
        let exit_code = Sys.command ("which "^prover^" > /dev/null 2>&1") in
        if exit_code > 0 then
          if  (Sys.file_exists prover) then
            let _ =
              (* if String.compare prover "oc" = 0 then *)
              (*   let () = Omega.is_local_solver := true in *)
              (*   let () = Omega.omegacalc := "./oc" in *)
              (*   () *)
              (* else *) if String.compare prover "z3" = 0 then
                (* let () = Globals.is_solver_local := true in *)
                let () = Z3.smtsolver_name := "./z3" in
                ()
              else ()
            in
            check_prover_existence rest
          else
            let () = print_string ("WARNING : Command for starting the prover (" ^ prover ^ ") not found\n") in
            exit 0
        else check_prover_existence rest

let is_smtsolver_z3 tp_str=
  String.compare tp_str "./z3" = 0 || String.compare tp_str "z3" = 0

let set_tp user_flag tp_str =
  prover_arg := tp_str;
  user_choice := user_flag;
  let prover_str = ref [] in
  (* if String.compare tp_str "./oc" = 0 || String.compare tp_str "oc" = 0 then *)
  (*   (Omega.omegacalc := tp_str; pure_tp := OmegaCalc; prover_str := "oc"::!prover_str;) *)
   (* else *)
    if is_smtsolver_z3 tp_str then
      (Z3.smtsolver_name := tp_str; pure_tp := Z3; prover_str := "z3"::!prover_str;)
    else
    ()
  (* if not !Globals.is_solver_local then check_prover_existence !prover_str else () *)

let start_prover () = match !pure_tp with
  (* | OmegaCalc ->   Omega.start_prover() ;*)
  | Z3 -> Z3.start();
  (* | LOG -> file_to_proof_log !Globals.source_files *)
  | _ -> Z3.start() (* Omega.start_prover() *)

let stop_prover () =
  begin
    match !pure_tp with
      (* | OmegaCalc -> ( Omega.stop() ;) *)
      | Z3 -> (Z3.stop();
        (*in the website, use z3, oc keeps running although hip is stopped*)
        (* if !Omega.is_omega_running then Omega.stop ()  ; *)
        )
      | _ -> Z3.stop(); (* Omega.stop(); *)
  end


let tp_is_sat_no_cache cex (f : CP.formula) (sat_no : string) =
  (* let omega_is_sat f = Omega.is_sat f sat_no in *)
  let z3_is_sat f = Z3.is_sat f sat_no cex in
  let res = (
    match !pure_tp with
   (*   | OmegaCalc -> (omega_is_sat f) *)
    | Z3 -> z3_is_sat f
    | _ -> z3_is_sat f (* omega_is_sat f *)
  )
  in
  res

let is_sat_chc pdecls f=
  let res = Z3Horn.is_sat_chc pdecls f (string_of_int !sat_subno) in
  let () = sat_subno := !sat_subno+1 in
  res

let is_sat_x cex (f : CP.formula) =
  let sat = tp_is_sat_no_cache cex f ( (string_of_int !sat_subno)) in
  let () = sat_subno := !sat_subno+1 in
  sat

let is_sat ?cex:(ce=false) f=
  Debug.no_1 "TP.is_sat" CP.string_of string_of_bool
      (fun _ -> is_sat_x ce f) f


let imply_x ante conseq imp_no timeout=
  (* let (pr_weak,pr_strong) = CP.drop_complex_ops in *)
  (* let (pr_weak_z3,pr_strong_z3) = CP.drop_complex_ops_z3 in *)
  let pr x = None in
  let (pr_weak,pr_strong) = pr, pr in
  (* let omega_imply a c = Omega.imply_ops pr_weak pr_strong a c imp_no timeout in *)
  let z3_imply a c = Z3.imply_ops_cex  a c false timeout in
  let r =
      match !pure_tp with
        (*| OmegaCalc ->
              (omega_imply ante conseq) *)
        | Z3 ->  z3_imply ante conseq
              (* | LOG -> find_bool_proof_res imp_no *)
        | _ -> z3_imply ante conseq
  in
  (* let tstop = Gen.Profiling.get_time () in *)
  Gen.Profiling.push_time "tp_is_sat";
  let () = Gen.Profiling.pop_time "tp_is_sat" in
  r

let imply ante conseq =
  let pr = CP.string_of in
  Debug.no_2 "TP.imply" pr pr string_of_bool
      (fun _ _ -> imply_x ante conseq "99" !VarGen.imply_timeout) ante conseq


let simplify (f : CP.formula) : CP.formula =
  (* Omega.simplify f *) f

let simplify f =
  let pr = CP.string_of in
  Debug.no_1 "TP.simplify" pr pr simplify f

let pairwisecheck (f : CP.formula) : CP.formula =
  (* Omega.pairwisecheck f *) f
