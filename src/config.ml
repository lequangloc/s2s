open Globals
open VarGen

let disable_printing ()=
  let () = VarGen.quiet_mode := true in
  let () = VarGen.enable_time_stats := false in
  ()

let parse_arguments = [
    ("-fe-core", Arg.Set_int Globals.fe, "use core parser as the font-end (smt2 is the default).");
    ("-print-parse", Arg.Set VarGen.print_parse, "print after parse.");
    ("-print-k", Arg.Set VarGen.print_k, "print k program.");
    ("-print-c", Arg.Set VarGen.print_core, "print core program.");
    ("-print-type", Arg.Set VarGen.print_type, "print core program.");
    ("-dis-print", Arg.Unit (fun _ -> disable_printing ()), "disable all printing.");
    ("-show-sat-proof", Arg.Set VarGen.sat_show_proof, "show the proofs of satisfiability.");
    ("-show-ent-proof", Arg.Set VarGen.ent_show_proof, "show the proofs of entailment.");
    ("-en-ecu", Arg.Set VarGen.ent_comp_linear_unfold, "enable composition unfolding for entailment checking.");
    ("-show-cex", Arg.Set VarGen.show_cex, "show the counterexamle.)");
    ("-show-ent-big", Arg.Set VarGen.ent_explicit_big_step, "show big steps.)");
    ("--sat-dis-base-reuse", Arg.Clear VarGen.sat_base_reuse, "dis reuse the base pair computed in the complete fragment");
    ("--ent-en-base-reuse", Arg.Set VarGen.ent_base_reuse, "reuse the base pair computed in the complete fragment");
    ("--ent-en-comp", Arg.Set VarGen.ent_composition_rule, "apply composition rule if applicable");
    ("--ent-dis-comp", Arg.Clear VarGen.ent_composition_rule, "do not apply compistion rule");

    ("--sat-bound", Arg.Set_int VarGen.sat_bound, "bound of SAT solver");
    ("--sat-dis-eager-return", Arg.Clear VarGen.sat_eager_return, "explore full proof for SAT");
    ("--en-smt-horn", Arg.Set Globals.smt_horn, "use z3 to solver chc");
    ("--dis-extend-htrue", Arg.Set VarGen.disable_extend_htrue, "not extend htrue in the lasso");
     ("--dis-infer-inv", Arg.Clear Globals.infer_inv, "disable inv inference for pred");
    ("-to-smt2", Arg.Set Globals.to_smt2, "convert the input to smt2 (for CVC4)");
    ("-to-smt2-trau", Arg.Set Globals.to_smt2_trau, "convert the input to smt2 (for Trau)");
    ("--inv", Arg.Set Globals.infer_inv, "Enable invariant inference for predicates");
    ("-debug", Arg.String (fun s ->
       Debug.z_debug_file:=s; z_debug_flag:=true),
   "Read from a debug log file");
]


let usage_msg = (Sys.argv.(0) ^" [options] \n")

let set_source_file arg =
  Globals.source_files := arg :: !Globals.source_files


let process_cmd_line () =
  Arg.parse parse_arguments set_source_file usage_msg
