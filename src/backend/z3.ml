
open Globals
open GlobProver
open Gen.Basic
open VarGen

module CP = Cpure

module StringSet = Set.Make(String)

let set_prover_type () = Others.Z3

let set_generated_prover_input = ref (fun _ -> ())
let set_prover_original_output = ref (fun _ -> ())

(* Pure formula printing function, to be intialized by cprinter module *)

let print_pure = CP.string_of
let print_ty_sv = Var.string_of

(***************************************************************
                  GLOBAL VARIABLES & TYPES
 **************************************************************)

(* Types for relations and ax(ioms*)
type rel_def = {
  rel_name : ident;
  rel_vars : Var.t list;
  related_rels : ident list;
  related_axioms : int list;
  rel_cache_smt_declare_fun : string;
}

let string_of_rel_def rd = rd.rel_name^(Var.string_of_list rd.rel_vars)
let eq_rel_def rd1 rd2 = rd1.rel_name = rd2.rel_name

(* TODO use hash table for fast retrieval *)
(* let global_rel_defs = ref ([] : rel_def list) *)
let global_rel_defs = new Gen.stack_pr "global_rel_defs" string_of_rel_def eq_rel_def


type axiom_type =
  | IMPLIES
  | IFF

type axiom_def = {
  axiom_direction   : axiom_type;
  axiom_hypothesis  : CP.formula;
  axiom_conclusion  : CP.formula;
  related_relations : ident list;
  axiom_cache_smt_assert : string;
}

(* TODO use hash table for fast retrieval *)
let global_axiom_defs = ref ([] : axiom_def list)

(* Record of information on a formula *)
type formula_info = {
  relations          : ident list; (* list of relations that the formula mentions *)
  axioms             : int list; (* list of related axioms (in form of position in the global list of axiom definitions) *)
}

(***************************************************************
            TRANSLATE CPURE FORMULA TO SMT FORMULA
 **************************************************************)

(* Construct [f(1) ... f(n)] *)
let rec generate_list n f =
  if (n = 0) then []
  else (generate_list (n-1) f) @ [f n]

(* Compute the n-th element of the sequence f0, f1, ..., fn defined by f0 = b and f_n = f(f_{n-1}) *)
let rec compute f n b =
  if (n = 0) then b
  else f (compute f (n-1) b)

let rec smt_of_typ t =
  match t with
  | Bool -> "Int" (* Use integer to represent Bool : 0 for false and > 0 for true. *)
  | Float -> "Real" (* Currently, do not support real arithmetic! *)
  | Int -> "Int"
  | UNK ->  "Int" (* illegal_format "z3.smt_of_typ: unexpected UNKNOWN type" *)
  | NUM -> "Int" (* Use default Int for NUM *)
  | BagT _ -> "Int"
  | TVar _ -> "Int"
  | Void -> "Int"
  | Named _ -> "Int" (* objects and records are just pointers *)
  | Array (et, d) -> compute (fun x -> "(Array Int " ^ x  ^ ")") d (smt_of_typ et)
  (* TODO *)
  | RelT _ -> "Int"
  | HpT -> "Int"
  | _ -> "Int"

let smt_of_typ t =
  Debug.no_1 "smt_of_typ" string_of_typ idf smt_of_typ t

let smt_of_var sv =
  (Var.name_of sv) ^ (if Var.is_primed sv then "_primed" else "")

let smt_of_typed_var sv =
  try
    "(" ^ (smt_of_var sv) ^ " " ^ (smt_of_typ (Var.type_of sv)) ^ ")"
  with _ ->
    illegal_format ("z3.smt_of_typed_var: problem with type of"^(Var.string_of sv))

let rec smt_of_exp a =
  let str = Exp.string_of a in
  match a with
  | Exp.Null _ -> "0"
  | Exp.Var (sv, _) -> smt_of_var sv
  | Exp.IConst (i, _) -> if i >= 0 then string_of_int i else "(- 0 " ^ (string_of_int (0-i)) ^ ")"
  | Exp.FConst (f, _) -> string_of_float f 
  | Exp.Add (a1, a2, _) -> "(+ " ^(smt_of_exp a1)^ " " ^ (smt_of_exp a2)^")"
  | Exp.Subtract (a1, a2, _) -> "(- " ^(smt_of_exp a1)^ " " ^ (smt_of_exp a2)^")"
  | Exp.Mult (a1, a2, _) -> "(* " ^ (smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | Exp.Div (a1, a2, _) -> "(/ " ^ (smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | Exp.Max _
  | Exp.Min _ -> illegal_format ("z3.smt_of_exp: min/max should not appear here")
  | Exp.Bag ([], _)
  | Exp.Bag _
  | Exp.BagUnion _
  | Exp.BagIntersect _
  | Exp.SConst _ | Exp.CConst _ | Exp.Concat _  | TypeCast _ | ArrayAt _
  | Exp.BagDiff _ -> illegal_format ("z3.smt_of_exp: ERROR in constraints (set/tup2) should not appear here : "  ^ str)

let rec smt_of_term pf =  match pf with
  | Term.BConst (c, _) -> if c then "true" else "false"
  | Term.BVar (sv, _) -> "(> " ^(smt_of_var sv) ^ " 0)"
  | Term.Lt (a1, a2, _) -> "(< " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | Term.Lte (a1, a2, _) -> "(<= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | Term.Gt (a1, a2, _) -> "(> " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | Term.Gte (a1, a2, _) -> "(>= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | Term.Eq (a1, a2, _) ->
        (*UNSOUND here: x=null & y=null ==> x=y *)
    (* if Exp.is_null a2 then *)
    (*   "(< " ^(smt_of_exp a1)^ " 1)" *)
    (* else if Exp.is_null a1 then *)
    (*   "(< " ^(smt_of_exp a2)^ " 1)" *)
    (* else *)
      "(= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | Term.Neq (a1, a2, _) ->
    (* if Exp.is_null a2 then *)
    (*   "(> " ^(smt_of_exp a1)^ " 0)" *)
    (* else if Exp.is_null a1 then *)
    (*   "(> " ^(smt_of_exp a2)^ " 0)" *)
    (* else *)
      "(not (= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ "))"
  | Term.EqMax (a1, a2, a3, _) ->
    let a1str = smt_of_exp a1 in
    let a2str = smt_of_exp a2 in
    let a3str = smt_of_exp a3 in
    "(or (and (= " ^ a1str ^ " " ^ a2str ^ ") (>= "^a2str^" "^a3str^")) (and (= " ^ a1str ^ " " ^ a3str ^ ") (< "^a2str^" "^a3str^")))"
  | Term.EqMin (a1, a2, a3, _) ->
    let a1str = smt_of_exp a1 in
    let a2str = smt_of_exp a2 in
    let a3str = smt_of_exp a3 in
    "(or (and (= " ^ a1str ^ " " ^ a2str ^ ") (< "^a2str^" "^a3str^")) (and (= " ^ a1str ^ " " ^ a3str ^ ") (>= "^a2str^" "^a3str^")))"
  (* UNHANDLED *)
  | Term.BagIn (v, e, l)    -> " in(" ^ (smt_of_var v) ^ ", " ^ (smt_of_exp e) ^ ")"
  | Term.BagNotIn (v, e, l) -> " NOT(in(" ^ (smt_of_var v) ^ ", " ^ (smt_of_exp e) ^"))"
  | Term.BagSub (e1, e2, l) -> " subset(" ^ smt_of_exp e1 ^ ", " ^ smt_of_exp e2 ^ ")"
  | Term.BagMax _ | Term.BagMin _ ->
    illegal_format ("z3.smt_of_b_formula: BagMax/BagMin should not appear here.\n")
  (* | CP.VarPerm _ -> illegal_format ("z3.smt_of_b_formula: Vperm should not appear here.\n") *)
  | Term.RelForm (r, args, l) ->
    let smt_args = List.map smt_of_exp args in
    (* special relation 'update_array' translate to smt primitive store in array theory *)
    let rn = (* Var.name_of *) r in
    if Term.is_update_array_relation rn then
      let orig_array = List.nth smt_args 0 in
      let new_array = List.nth smt_args 1 in
      let value = List.nth smt_args 2 in
      let index = List.rev (List.tl (List.tl (List.tl smt_args))) in
      let last_index = List.hd index in
      let rem_index = List.rev (List.tl index) in
      let arr_select = List.fold_left (fun x y -> let k = List.hd x in ("(select " ^ k ^ " " ^ y ^ ")") :: x) [orig_array] rem_index in
      let arr_select = List.rev arr_select in
      let fl = List.map2 (fun x y -> (x,y)) arr_select (rem_index @ [last_index]) in
      let result = List.fold_right (fun x y -> "(store " ^ (fst x) ^ " " ^ (snd x) ^ " " ^ y ^ ")") fl value in
      "(= " ^ new_array ^ " " ^ result ^ ")"
    else
      "(" ^ ((* Var.name_of *) r) ^ " " ^ (String.concat " " smt_args) ^ ")"
(* | CP.XPure _ -> Error.report_no_pattern () *)

let rec smt_of_formula  f =
  let rec helper f= (
    match f with
    | CP.BForm bf -> (
        (smt_of_term bf)
      )
    | CP.And (p1, p2) -> "(and " ^ (helper p1) ^ " " ^ (helper p2) ^ ")"
    | CP.Or (p1, p2) -> "(or " ^ (helper p1) ^ " " ^ (helper p2) ^ ")"
    | CP.Not (p) -> "(not " ^ (smt_of_formula p) ^ ")"
    | CP.Forall (sv, p) ->
      "(forall (" ^ (smt_of_typed_var sv) ^ ") " ^ (helper p) ^ ")"
    | CP.Exists (sv, p) ->
      "(exists (" ^ (smt_of_typed_var sv) ^ ") " ^ (helper p) ^ ")"
  ) in
  helper f

let smt_of_formula f =
  Debug.no_1 "smt_of_formula"  CP.string_of idf
    (fun _ -> smt_of_formula  f) f


(***************************************************************
                       FORMULA INFORMATION
 **************************************************************)

(* Default info, returned in most cases *)
let default_formula_info = {
    relations = [];
    axioms = [];
}

(* Collect information about a formula f or combined information about 2 formulas *)
let rec collect_formula_info f = 
  let info = collect_formula_info_raw f in
  let indirect_relations = List.flatten (List.map (fun x -> if (List.mem x.rel_name info.relations) then x.related_rels else []) global_rel_defs # get_stk) in
  let all_relations = Gen.BList.remove_dups_eq (=) (info.relations @ indirect_relations) in
  let all_axioms = List.flatten (List.map (fun x -> if (List.mem x.rel_name all_relations) then x.related_axioms else []) global_rel_defs # get_stk) in
  let all_axioms = Gen.BList.remove_dups_eq (=) all_axioms in
  { relations = all_relations;
    axioms = all_axioms;}

and collect_combine_formula_info f1 f2 = 
  compact_formula_info (combine_formula_info (collect_formula_info f1) (collect_formula_info f2))

(* Recursively collect the information based on the structure of 
 * the formula. This information might not be complete due to cross reference.
 * For instance, a relation definition might refers to other relations. This
 * function is only used mainly in pre-computing information of relation and
 * axiom definition.
 * The information is to be corrected by the function collect_formula_info.
*)
and collect_formula_info_raw f = match f with
  | CP.BForm b -> collect_bformula_info b
  | CP.And (f1,f2)  | CP.Or (f1,f2) -> 
    collect_combine_formula_info_raw f1 f2
  | CP.Not (f1) -> collect_formula_info_raw f1
  | CP.Forall (svs,f1) | CP.Exists (svs,f1) -> collect_formula_info_raw f1

and collect_combine_formula_info_raw f1 f2 =
  combine_formula_info (collect_formula_info_raw f1) (collect_formula_info_raw f2)

and collect_bformula_info b = match b with
  | Term.RelForm (r,args,_) ->
    (* let r = Var.name_of r in *)
    if r = "update_array" then
      default_formula_info
    else
      { default_formula_info with relations = [r]; }
  | _ -> default_formula_info


and combine_formula_info if1 if2 =
  { relations = List.append if1.relations if2.relations;
    axioms = Gen.BList.remove_dups_eq (=) (List.append if1.axioms if2.axioms); }

and compact_formula_info info =
  { relations = Gen.BList.remove_dups_eq (=) info.relations;
    axioms = Gen.BList.remove_dups_eq (=) info.axioms; }

(***************************************************************
                      AXIOMS AND RELATIONS
 **************************************************************)

(* Interface function to add a new axiom *)
let add_axiom h dir c =
  (* let () = print_endline ("Add axiom : " ^ (!print_pure h) ^ (match dir with |IFF -> " <==> " | _ -> " ==> ") ^ (!print_pure c)) in *)
  let info = collect_combine_formula_info_raw h c in
  (* assumption: at the time of adding this axiom, all relations in global_rel_defs has their related axioms computed *)
  let indirectly_related_relations = List.filter (fun x -> List.mem x.rel_name info.relations) global_rel_defs # get_stk in
  let indirectly_related_relations = List.map (fun x -> x.related_rels) indirectly_related_relations in
  let related_relations = info.relations @ (List.flatten indirectly_related_relations) in
  let related_relations = Gen.BList.remove_dups_eq (=) related_relations in
  (* let () = print_endline ("All related relations found : " ^ (String.concat ", " related_relations) ^ "\n") in *)
  let aindex = List.length !global_axiom_defs in (
    (* Modifying every relations appearing in h and c by
       1)   Add reference to 'h dir c' as a related axiom
       2)   Add all other relations (appearing in h and c) to the list of related relations *)
    let new_rel_defs =  List.map (fun x ->
        if (List.mem x.rel_name related_relations) then
          let rs = Gen.BList.remove_dups_eq (fun s1 s2 -> String.compare s1 s2 =0) (x.related_rels @ related_relations) in
          { x with 
            related_rels = rs;
            related_axioms = x.related_axioms @ [aindex]; }
        else x
      ) global_rel_defs # get_stk in
    global_rel_defs # reset_pr;
    global_rel_defs # push_list_pr new_rel_defs;
    (* Cache the SMT input for 'h dir c' so that we do not have to generate this over and over again *)
    let params = List.append (CP.fv h) (CP.fv c) in
    let rel_ids = List.map (fun r -> {Var.t= RelT[]; Var.id = r.rel_name; Var.p=Unprimed}) global_rel_defs # get_stk in
    let params = Gen.BList.difference_eq Var.equal params rel_ids in
    let params = Gen.BList.remove_dups_eq Var.equal params in
    let smt_params = String.concat " " (List.map smt_of_typed_var params) in
    let op = match dir with 
      | IMPLIES -> "=>" 
      | IFF -> "=" in
    let cache_smt_input = (
      "(assert " ^ 
      (if params = [] then "" else "(forall (" ^ smt_params ^ ")\n") ^
      "\t(" ^ op ^ " " ^ (smt_of_formula h) ^ 
      "\n\t" ^ (smt_of_formula c) ^ ")" ^ (* close the main part of the axiom *)
      (if params = [] then "" else ")") (* close the forall if added *) ^ ")\n" (* close the assert *) 
    ) in
    (* Add 'h dir c' to the global axioms *)
    let new_axiom = {
      axiom_direction = dir;
      axiom_hypothesis = h;
      axiom_conclusion = c;
      related_relations = related_relations (* info.relations TODO must we compute closure ? *);
      axiom_cache_smt_assert = cache_smt_input; 
    } in
    global_axiom_defs := !global_axiom_defs @ [new_axiom];
  )

(* Interface function to add a new relation *)
let add_relation (rname1:string) rargs rform =
  let rname = {Var.t = RelT[]; Var.id = rname1; Var.p = Unprimed} in
  if (Term.is_update_array_relation rname1) then 
    ()
  else (
    (* Cache the declaration for this relation *)
    let cache_smt_input = (
      let signature = List.map Var.type_of rargs in
      let smt_signature = String.concat " " (List.map smt_of_typ signature) in
      (* Declare the relation in form of a function --> Bool *)
      "(declare-fun " ^ rname1 ^ " (" ^ smt_signature ^ ") Bool)\n"
    ) in
    let rdef = {
      rel_name = rname1; 
      rel_vars = rargs;
      related_rels = []; (* to be filled up by add_axiom *)
      related_axioms = []; (* to be filled up by add_axiom *)
      rel_cache_smt_declare_fun = cache_smt_input;
    } in
    global_rel_defs # push_list_pr [rdef];
    (* Note that this axiom must be NEW i.e. no relation with this name is added earlier so that add_axiom is correct *)
    match rform with
    | CP.BForm (Term.BConst (true, no_pos)) (* no definition supplied *) -> (* do nothing *) ()
    | _ -> (* add an axiom to describe the definition *)
          let h = CP.BForm (Term.RelForm ((*rname*) rname1, List.map (fun x -> Exp.mkVar x no_pos) rargs, no_pos)) in
      add_axiom h IFF rform;
  )

(* Interface function to add a new hp relation *)
let add_hp_relation (rname1:string) rargs rform =
  (* let rname = CP.SpecVar(HpT,rname1,Unprimed) in *)
  (* Cache the declaration for this relation *)
  let cache_smt_input = (
    let signature = List.map Var.type_of rargs in
    let smt_signature = String.concat " " (List.map smt_of_typ signature) in
    (* Declare the relation in form of a function --> Bool *)
    "(declare-fun " ^ rname1 ^ " (" ^ smt_signature ^ ") Bool)\n"
  ) in
  let rdef = { rel_name = rname1;
               rel_vars = rargs;
               related_rels = []; (* to be filled up by add_axiom *)
               related_axioms = []; (* to be filled up by add_axiom *)
               rel_cache_smt_declare_fun = cache_smt_input; } in
  global_rel_defs # push_list_pr [rdef];
  (* Note that this axiom must be NEW i.e. no relation with this name is added earlier so that add_axiom is correct *)

  (***************************************************************
                              INTERACTION
   **************************************************************)

type sat_type =
  | Sat    (* solver returns sat *)
  | UnSat    (* solver returns unsat *)
  | Unknown  (* solver returns unknown or there is an exception *)
  | Aborted (* solver returns an exception *)

(* Record structure to store information parsed from the output
 * of the SMT solver.
 * This change is to make development extensible in later stage.
*)
type smt_output = {
  original_output_text : string list;   (* original (command line) output text of the solver; included in order to support printing *)
  sat_result : sat_type; (* satisfiability information *)
  (* expand with other information : proof, time, error, warning, ... *)
}

let string_of_smt_output output =
  (String.concat "\n" output.original_output_text)

let rec icollect_output2 chn accumulated_output : string list =
  let output =
    try
      let line = input_line chn in
      if (line = "unsat") then
        let _ = input_line chn in
        accumulated_output @ [line]
      else if (line = ")") then
        accumulated_output @ [line]
      else
        icollect_output2 chn (accumulated_output @ [line])
    with
    | End_of_file -> accumulated_output in
  output

(* Collect all Z3's output into a list of strings *)
let rec icollect_output chn accumulated_output : string list =
  let output =
    try
      let line = input_line chn in
      (* let () = print_endline ("locle2" ^ line) in *)
      if ((String.length line) > 7) then (*something diff to sat/unsat/unknown, retry-may lead to timeout here*)
        icollect_output chn (accumulated_output @ [line])
      else accumulated_output @ [line]
    with | End_of_file -> accumulated_output in
  output


let rec collect_output chn accumulated_output : string list =
  let output =
    try
      let line = input_line chn in
      (* let () = print_endline ("locle: " ^ line) in *)
      collect_output chn (accumulated_output @ [line])
    with | End_of_file -> accumulated_output in
  output

let sat_type_from_string r input =
  if (String.compare r "sat" == 0) then Sat
  else if (String.compare r "unsat" == 0) then UnSat
  else
    try
      let todo_var_unknown:int = Str.search_forward (Str.regexp "unexpected") r 0 in
      (print_string "Z3 translation failure!";
       Error.report_error { 
         Error.error_loc = no_pos; 
         Error.error_text =("Z3 translation failure!!\n"^r^"\n input: "^input)})
    with
    | Not_found -> Unknown

let parse_model_to_pure_formula model =
  let rec helper acc model =
    let line = List.hd model in
    if line = ")" then acc
    else
      let line2 = List.hd (List.tl model) in
      let var = String.sub line 14 ((String.rindex line '(') - 15) in
      let var = Exp.mkVar (Var.mk_unprimed Globals.Int var) no_pos in
      let value = String.sub line2 4 ((String.length line2) - 5) in
      let value =
        try
          let i = String.index value '-' in
          let l = String.length value in
          Exp.mkIConst (0 - (int_of_string (String.sub value (i + 2) (l - i - 3)))) no_pos
        with Not_found -> Exp.mkIConst (int_of_string value) no_pos
      in
      let pf = CP.mkEqExp var value no_pos in
      let new_acc = Cpure.mkAnd acc pf no_pos in
      helper new_acc (List.tl (List.tl model))
  in
  let pf = helper (Cpure.mkTrue no_pos) (List.tl model) in
  pf

let iget_answer2 chn input =
  let output = icollect_output2 chn [] in
  let solver_sat_result = List.hd output (* List.nth output (List.length output - 1) *) in
  let model = List.tl output in
  let unknown = List.map (fun s -> print_endline s) model in
  let _ =
    if solver_sat_result = "sat" then
      parse_model_to_pure_formula model
    else
      Cpure.mkTrue no_pos
  in
  { original_output_text = output;
    sat_result = sat_type_from_string solver_sat_result input; }

let iget_answer chn input =
  let check_error_msg s=
    try
      (* let _ = print_endline ("s : " ^ s) in *)
      let _ = Str.search_forward (Str.regexp "error ") s 0 in
      let _ = Error.report_warning { Error.error_loc = no_pos; Error.error_text =("Z3 error message: "^s)} in
      true
    with _ -> false
  in
  let output = icollect_output chn [] in
  let solver_sat_result = List.nth output (List.length output - 1) in
  let last_z3_sat_type = sat_type_from_string solver_sat_result input in
  let st = if List.length output > 1 then
      try
        let b = List.fold_left (fun old_b s -> old_b || (check_error_msg s)) false output in
        (* if b then Sat else *) last_z3_sat_type
      with _ -> last_z3_sat_type
    else last_z3_sat_type
  in
  { original_output_text = output;
    sat_result =  st; }

let get_answer chn input =
  let output = collect_output chn [] in
  let solver_sat_result = List.nth output (List.length output - 1) in
  { original_output_text = output;
    sat_result = sat_type_from_string solver_sat_result input; }

let remove_file filename =
  try Sys.remove filename;
  with | e -> ignore e

type smtprover = Z3

(* Global settings *)
let infile = "/tmp/in" ^ (string_of_int (Unix.getpid ())) ^ ".smt2"
let outfile = "/tmp/out" ^ (string_of_int (Unix.getpid ()))
let z3_sat_timeout_limit = 20.0
let prover_pid = ref 0

let z3_call_count: int ref = ref 0
let is_z3_running = ref false

let smtsolver_name = ref ("z3": string)

let prover_process = ref {
    name = !smtsolver_name;
    pid = 0;
    inchannel = stdin;
    outchannel = stdout;
    errchannel = stdin
  }


let global_z3 = "z3"

let smtsolver_path = "z3"


(***********)
let test_number = ref 0
let last_test_number = ref 0
let log_all_flag = ref false
let z3_restart_interval = ref (-1)
let log_all = ("allinput.z3")


let set_process (proc: prover_process_t) =
  prover_process := proc


let rec prelude () = ()

(* start z3 system in a separated process and load redlog package *)
and start() =
  try (
    if not !is_z3_running then (
        print_string_if (not !quiet_mode) "Starting z3... \n"; flush stdout;
      last_test_number := !test_number;
      let () = (
          Procutils.PrvComms.start !log_all_flag log_all (!smtsolver_name, smtsolver_path, [|smtsolver_path; "-smt2"; "-in"; "unsat_core=true"|]) set_process prelude
      ) in
      is_z3_running := true;
    )
  )
  with e -> (
      if (!quiet_mode) then (
        print_endline_quiet "Unable to run the prover Z3!";
        print_endline_quiet ("Please make sure its executable file (" ^ !smtsolver_name ^ ") is installed")
      );
      raise e
    )

(* stop Z3 system *)
let stop () =
  if !is_z3_running then (
    let num_tasks = !test_number - !last_test_number in
    print_string_if (not !VarGen.quiet_mode && !Globals.enable_count_stats) ("Stop z3... "^(string_of_int !z3_call_count)^" invocations "); flush stdout;
    let () = Procutils.PrvComms.stop !log_all_flag log_all !prover_process num_tasks Sys.sigkill (fun () -> ()) in
    is_z3_running := false;
  )

(* restart Z3 system *)
let restart reason =
  if !is_z3_running then (
    let () = print_string_if !Globals.enable_count_stats (reason^" Restarting z3 after ... "^(string_of_int !z3_call_count)^" invocations. ") in
    Procutils.PrvComms.restart !log_all_flag log_all reason "z3" start stop
  ) else (
    let () = print_string_if !Globals.enable_count_stats (reason^" not restarting z3 ... "^(string_of_int !z3_call_count)^" invocations ") in
    ()
  )

(* send formula to z3 and receive result -true/false/unknown*)
let check_formula_x f bget_cex timeout =
  let tstartlog = Gen.Profiling.get_time () in
  if not !is_z3_running then start ()
  else if (!z3_call_count = !z3_restart_interval) then (
    restart("Regularly restart:1 ");
    z3_call_count := 0;
  );
  let fnc f = (
    let () = incr z3_call_count in
    let new_f = "(push)\n" ^ f ^ "(pop)\n" in
    let _= if(!proof_logging_txt) then add_to_z3_proof_log_list new_f in
    (* Debug.info_hprint (add_str "z3" pr_id) new_f no_pos; *)
    output_string (!prover_process.outchannel) new_f;
    flush (!prover_process.outchannel);
    if bget_cex then
      iget_answer2 (!prover_process.inchannel) f
    else
      iget_answer (!prover_process.inchannel) f
  ) in
  let fail_with_timeout () = (
      let to_msg = if !quiet_mode then ""
      else "[z3.ml]Timeout when checking sat!" ^ (string_of_float timeout) in
    restart (to_msg);
    { original_output_text = []; sat_result = Unknown; }
  ) in
  let res = Procutils.PrvComms.maybe_raise_and_catch_timeout fnc f timeout fail_with_timeout in
  let tstoplog = Gen.Profiling.get_time () in
  let _= Globals.z3_time := !Globals.z3_time +. (tstoplog -. tstartlog) in
  res

let check_formula f bget_cex timeout =
  Debug.no_3 "Z3:check_formula" idf string_of_bool
      string_of_float string_of_smt_output
    check_formula_x f bget_cex timeout

let check_formula f bget_cex timeout =
  Gen.Profiling.no_2 "smt_check_formula" check_formula f bget_cex timeout

(***************************************************************
   GENERATE SMT INPUT FOR IMPLICATION/SATISFIABILITY CHECKING
 **************************************************************)


(**
 * Logic types for smt solvers
 * based on smt-lib benchmark specs
*)
type smtlogic =
  | QF_IDL    (* Closed quantifier-free integer *)
  | QF_LIA    (* quantifier free linear integer arithmetic *)
  | QF_NIA    (* quantifier free nonlinear integer arithmetic *)
  | AUFLIA    (* arrays, uninterpreted functions and linear integer arithmetic *)
  | UFNIA     (* uninterpreted functions and nonlinear integer arithmetic *)

let string_of_logic logic =
  match logic with
    | QF_IDL -> "QF_IDL"
    | QF_LIA -> "QF_LIA"
    | QF_NIA -> "QF_NIA"
    | AUFLIA -> "AUFLIA"
    | UFNIA -> "UFNIA"

let smt_var_decl v=
  let tp = (Var.type_of v)in
    let t = smt_of_typ tp in
    (* match tp with *)
    (* | FuncT _ -> "(declare-fun " ^ (smt_of_var v) ^ " " ^ t ^ ")\n" *)
    (* | _ -> *) "(declare-fun " ^ (smt_of_var v) ^ " () " ^ (t) ^ ")\n"

let smt_var_decls fvars = String.concat "" (List.map  smt_var_decl fvars)

(* output for smt-lib v2.0 format *)
let to_smt_v2 ante conseq fvars0 info bget_cex =
  (* Variable declarations *)
  (*let _ = List.map (fun c -> print_string(" "^(!print_ty_sv c))) fvars in*)
  let fvars = List.filter (fun sv -> not (Var.is_rel_typ sv)) (Var.remove_dups fvars0) in
  let smt_var_decls = smt_var_decls fvars in
  (* Relations that appears in the ante and conseq *)
  let used_rels = info.relations in
  let rel_decls = String.concat "" (List.map (fun x -> x.rel_cache_smt_declare_fun) global_rel_defs # get_stk) in
  (* let _ = Debug.info_hprint (add_str "rel_decls" (pr_id)) rel_decls no_pos in *)
  let rel_decls = String.concat "" (List.map (fun x -> if (List.mem x.rel_name used_rels) then x.rel_cache_smt_declare_fun else "") global_rel_defs # get_stk) in
  (* Necessary axioms *)
  (* let axiom_asserts = String.concat "" (List.map (fun x -> x.axiom_cache_smt_assert) !global_axiom_defs) in *) (* Add all axioms; in case there are bugs! *)
  let axiom_asserts = String.concat "" (List.map (fun ax_id ->
      (* let _ = Debug.info_hprint (add_str " ax_id" (string_of_int))  ax_id no_pos in *)
      let ax = List.nth !global_axiom_defs ax_id in
      ax.axiom_cache_smt_assert) info.axioms) in
  (* Antecedent and consequence : split /\ into small asserts for easier management *)
  let ante_clauses = CP.split_conjunctions ante in
  let ante_clauses = Gen.BList.remove_dups_eq CP.equal ante_clauses in
  let ante_strs = List.map (fun x -> "(assert " ^ (smt_of_formula x) ^ ")\n") ante_clauses in
  let ante_str = String.concat "" ante_strs in
  let conseq_str = smt_of_formula conseq in (
     (* "(set-logic QF_EUF)\n" ^ *)
    ";Variables declarations\n" ^ 
    smt_var_decls ^
    ";Relations declarations\n" ^ 
    rel_decls ^
    ";Axioms assertions\n" ^ 
    axiom_asserts ^
    ";Antecedent\n" ^ 
    ante_str ^
    ";Negation of Consequence\n" ^ "(assert (not " ^ conseq_str ^ "))\n" ^
    "(check-sat)" ^
    (if bget_cex then "\n(get-model)" else "")
  )

(* output for smt-lib v1.2 format *)
and to_smt_v1 ante conseq logic fvars =
  let rec defvars vars = match vars with
    | [] -> ""
    | var::rest -> "(" ^ (smt_of_var var) ^ " Int) " ^ (defvars rest)
  in
  (* let () = print_endline ("#### ante = " ^ (!CP.print_formula ante)) in *)
  let ante = smt_of_formula ante in
  let conseq = smt_of_formula conseq in
  (*--------------------------------------*)
  let extrafuns = 
    if fvars = [] then "" 
    else ":extrafuns (" ^ (defvars fvars) ^ ")\n"
  in (
    "(benchmark blahblah \n" ^
    ":status unknown\n" ^
    ":logic " ^ (string_of_logic logic) ^ "\n" ^
    extrafuns ^
    ":assumption " ^ ante ^ "\n" ^
    ":formula (not " ^ conseq ^ ")\n" ^
    ")"
  )

(* Converts a core pure formula into SMT-LIB format which can be run through various SMT provers. *)
let to_smt_x (ante : CP.formula) (conseq : CP.formula option)  bget_cex: string =
  let conseq = match conseq with
    (* is_sat checking *)
    | None -> CP.mkFalse no_pos
    | Some f -> f
  in
  let conseq_info = collect_formula_info conseq in
  (* remove occurences of dom in ante if conseq has nothing to do with dom *)
  let ante =
    if (not (List.mem "dom" conseq_info.relations)) then
      CP.remove_primitive (fun x ->
          match x with
            | Term.RelForm (r, _ , _) -> (* Var.name_of *) r = "dom"
            | _ -> false
      ) ante
    else ante in
  let _ = Debug.ninfo_hprint (add_str "ante" CP.string_of) ante no_pos in
  let ante_info = collect_formula_info ante in
  let info = combine_formula_info ante_info conseq_info in
  let ante_fv = CP.fv ante in
  let conseq_fv = CP.fv conseq in
  let all_fv = Var.remove_dups (ante_fv @ conseq_fv) in
  let _ = Debug.ninfo_hprint (add_str "all_fv" Var.string_of_full_list) all_fv no_pos in
  let res = to_smt_v2 ante conseq all_fv info bget_cex in
  (* let () = print_endline (" ### res = \n " ^ res) in *)
  res

let to_smt  (ante : CP.formula) (conseq : CP.formula option)  bget_cex =
  let pr = CP.string_of in
  Debug.no_2 "to_smt" pr (pr_option pr) pr_id
      (fun _ _ -> to_smt_x ante conseq  bget_cex) ante conseq

(***************************************************************
                         CONSOLE OUTPUT
 **************************************************************)

type output_configuration = {
    print_implication            : bool ref; (* print the implication problems sent to this smt_imply *)
    suppress_print_implication   : bool ref; (* temporary suppress all printing *)
}

(* Global collection of printing control switches, set by scriptarguments *)
let outconfig = {
    print_implication = ref false;
    suppress_print_implication = ref false;
}

(* Function to suppress and unsuppress all output of this modules *)

let suppress_all_output () = outconfig.suppress_print_implication := true

let unsuppress_all_output () = outconfig.suppress_print_implication := false

let process_stdout_print ante conseq input output res =
  if (not !(outconfig.suppress_print_implication)) then
    begin
      if !(outconfig.print_implication) then
        print_endline_quiet ("CHECKING IMPLICATION:\n\n" ^ (print_pure ante) ^ " |- " ^ (print_pure conseq) ^ "\n");
      if !(Globals.print_original_solver_input) then (
        print_endline_quiet (">>> GENERATED SMT INPUT:\n\n" ^ input);
        flush stdout;
      );
      if !(Globals.print_original_solver_output) then (
        print_endline_quiet (">>> Z3 OUTPUT RECEIVED:\n" ^ (string_of_smt_output output));
        print_endline_quiet (match output.sat_result with
            | UnSat -> ">>> VERDICT: UNSAT/VALID!"
            | Sat -> ">>> VERDICT: FAILED!"
            | Unknown -> ">>> VERDICT: UNKNOWN! CONSIDERED AS FAILED."
            | Aborted -> ">>> VERDICT: ABORTED! CONSIDERED AS FAILED.");
        flush stdout;
      );
      if (!(outconfig.print_implication) || !(Globals.print_original_solver_input) || !(Globals.print_original_solver_output)) then
        print_string_quiet "\n";
    end

(**************************************************************
   MAIN INTERFACE : CHECKING IMPLICATION AND SATISFIABILITY
 *************************************************************)

let try_induction = ref false
let max_induction_level = ref 0

(**
 * Select the candidates to do induction on. Just find all
 * relation dom(_,low,high) that appears and collect the
 * { high - low } such that ante |- low <= high.
*)
let rec collect_induction_value_candidates (ante : CP.t) (conseq : CP.t) : (Exp.t list) =
  (*let () = print_string ("collect_induction_value_candidates :: ante = " ^ (!print_pure ante) ^ "\nconseq = " ^ (!print_pure conseq) ^ "\n") in*)
  match conseq with
  | CP.BForm p -> (
      match p with
      | Term.RelForm (r,[value],_) ->
        if ((* Var.name_of *) r) ="induce" then [value]
        else []
      | _ -> []
    )
  | CP.And (f1,f2) -> (collect_induction_value_candidates ante f1) @ (collect_induction_value_candidates ante f2)
  | CP.Or (f1,f2) -> (collect_induction_value_candidates ante f1) @ (collect_induction_value_candidates ante f2)
  | CP.Not (f) -> (collect_induction_value_candidates ante f)
  | CP.Forall _ | CP.Exists _ -> []

(**
    * Select the value to do induction on.
    * A simple approach : induct on the length of an array.
*)
and choose_induction_value (ante : CP.t) (conseq : CP.t) (vals : Exp.t list) : Exp.t =  List.hd vals


(**
    * Create a variable totally different from the ones in vlist.
*)
and create_induction_var (vlist : Var.t list) : Var.t =
  (*let () = print_string "create_induction_var\n" in*)
  (* We select the appropriate variable with name "omg_i"*)
  (* with i minimal natural number such that omg_i is not in vlist *)
  let rec create_induction_var_helper vlist i = (
    match vlist with
    | [] -> i
    | hd :: tl ->
      let v = {Var.t = Int; Var.id = "omg_" ^ (string_of_int i); Var.p=Unprimed} in
      if List.mem v vlist then
        create_induction_var_helper tl (i+1)
      else 
        create_induction_var_helper tl i
  ) in let i = create_induction_var_helper vlist 0 in
  Var.mk Int ("omg_" ^ (string_of_int i)) Unprimed

(**
    * Generate the base case, induction hypothesis and induction case
    * for Ante -> Conseq
*)


and has_exists conseq =
  match conseq with
  | CP.Exists _ -> true
  | _ -> false

(**
 * Test for satisfiability
 * We also consider unknown is the same as sat
*)
let smt_is_sat (f : Cpure.t) (sat_no : string) timeout bget_cex: bool =
  let input = to_smt f None bget_cex in
  let output = (
      check_formula input bget_cex timeout
  ) in
  let res = match output.sat_result with
    | UnSat -> false
    | _ -> true in
  let () = process_stdout_print f (CP.mkFalse no_pos) input output res in
  res

let is_sat_x (pe : CP.formula) sat_no bget_cex: bool =
  try
    smt_is_sat pe sat_no z3_sat_timeout_limit bget_cex
  with Illegal_Prover_Format s ->
    print_endline_quiet ("\nWARNING : Illegal_Prover_Format for :"^s);
    print_endline_quiet ("Apply z3.is_sat on formula :"^(print_pure pe));
    flush stdout;
    failwith s

let is_sat f sat_no bget_cex=
  let pr = CP.string_of in
  Debug.no_2 "z3.is_sat" pr (fun x->x) string_of_bool
      (fun _ _ -> is_sat_x f sat_no bget_cex) f sat_no


(* Template Solving by Z3 *)
open Z3m

let smt_timeout = ref 5.0

let push_smt_input is_opt inp timeout f_timeout =
  let tstartlog = Gen.Profiling.get_time () in
  if not !is_z3_running then start ()
  else if (!z3_call_count = !z3_restart_interval) then (
    restart("Regularly restart: 1 ");
    z3_call_count := 0;
  );
  let fnc f = (
    let () = incr z3_call_count in
    let new_f = if not is_opt then "(push)\n" ^ f ^ "(pop)\n" else f in
    (* let () = x_tinfo_hp (add_str "SMT input" idf) new_f no_pos in *)
    let () = if (!proof_logging_txt) then add_to_z3_proof_log_list new_f in
    output_string (!prover_process.outchannel) new_f;
    flush (!prover_process.outchannel)) in
  let res = Procutils.PrvComms.maybe_raise_and_catch_timeout fnc inp timeout f_timeout in
  let tstoplog = Gen.Profiling.get_time () in
  let () = Globals.z3_time := !Globals.z3_time +. (tstoplog -. tstartlog) in
  res

let get_model is_linear vars assertions =
  (* Variable declarations *)
  let smt_var_decls = List.map (fun v ->
      let typ = (Var.type_of v)in
      let t = smt_of_typ typ in
      "(declare-const " ^ (smt_of_var v) ^ " " ^ t ^ ")\n"
    ) vars in
  let smt_var_decls = String.concat "" smt_var_decls in

  let smt_asserts = List.map (fun a ->
      "(assert " ^ (smt_of_formula a) ^ ")\n") assertions in
  let smt_asserts = String.concat "" smt_asserts in
  let smt_inp =
    ";Variables Declarations\n" ^ smt_var_decls ^
    ";Assertion Declations\n" ^ smt_asserts ^
    (if is_linear then "(check-sat)" else "(check-sat-using qfnra-nlsat)") ^ "\n" ^
    (* "(check-sat)\n" ^ *)
    "(get-model)\n"
  in


  let fail_with_timeout _ = (
    restart ("[z3.ml] Timeout when getting model!"
    ^ (string_of_float !smt_timeout))
  ) in
  let () = push_smt_input false smt_inp !smt_timeout fail_with_timeout in

  let r =
    try
      let lexbuf = Lexing.from_channel !prover_process.inchannel in
      Z3mparser.output Z3mlexer.tokenizer lexbuf
    with _ -> Sat_or_Unk []
  in r

let get_model is_linear vars assertions =
  let pr1 = pr_list CP.string_of in
  let pr2 = string_of_z3m_res in
  Debug.no_1 "z3_get_model" pr1 pr2
    (fun _ -> get_model is_linear vars assertions) assertions

let norm_model (m: (string * z3m_val) list): (string * int) list =
  let vl, il = List.split m in
  let il = z3m_val_to_int il in
  let m = List.combine vl il in
  m

let norm_model (m: (string * z3m_val) list): (string * int) list =
  let pr1 = pr_list (pr_pair idf string_of_z3m_val) in
  let pr2 = pr_list (pr_pair idf string_of_int) in
  Debug.no_1 "z3_norm_model" pr1 pr2
    norm_model m

let assert_label_prefix = "z3_l_"

let init_unsat_cores_option = ref false

let set_unsat_cores_option () =
  if not !init_unsat_cores_option then
    let smt_inp = "(set-option :produce-unsat-cores true)\n" in
    let fail_with_timeout _ = (
      restart ("[smtsolver.ml] Timeout when getting model!" ^ (string_of_float !smt_timeout))
    ) in
    init_unsat_cores_option := true;
    push_smt_input true smt_inp !smt_timeout fail_with_timeout
  else ()

let get_unsat_core assertions =
  let vars = Gen.BList.remove_dups_eq Var.equal (List.concat (List.map CP.fv assertions)) in
  (* Variable declarations *)
  let smt_var_decls = List.map (fun v ->
      let typ = (Var.type_of v)in
      let t = smt_of_typ typ in
      "(declare-const " ^ (smt_of_var v) ^ " " ^ t ^ ")\n"
    ) vars in
  let smt_var_decls = String.concat "" smt_var_decls in

  let assertions_w_label = fst (List.fold_left (fun (acc, i) a ->
      acc @ [(i + 1, a)], i + 1) ([], 0) assertions) in
  let smt_asserts = List.map (fun (i, a) ->
      let label = assert_label_prefix ^ (string_of_int i) in
      "(assert (! " ^ (smt_of_formula a) ^ " :named " ^ label ^ "))\n") assertions_w_label in
  let smt_asserts = String.concat "" smt_asserts in
  let smt_inp =
    (* "(set-option :produce-unsat-cores true)\n" ^ *)
    ";Variables Declarations\n" ^ smt_var_decls ^
    ";Assertion Declations\n" ^ smt_asserts ^
    "(check-sat)\n" ^
    "(get-unsat-core)\n"
  in

  (* let () = print_endline ("smt_inp: \n" ^ smt_inp) in *)

  let fail_with_timeout _ = (
    restart ("[smtsolver.ml] Timeout when getting model!" ^ (string_of_float !smt_timeout))
  ) in
  (* let () = set_unsat_cores_option () in *)
  let () = push_smt_input false smt_inp !smt_timeout fail_with_timeout in

  let eq_str s1 s2 = String.compare s1 s2 == 0 in

  let lexbuf = Lexing.from_channel !prover_process.inchannel in
  let unsat_core =
    try
      let r = Z3mparser.output_unsat_core Z3mlexer.tokenizer lexbuf in

      match r with
      | Sat_or_Unk _ -> []
      | Unsat unsat_core_ids ->
        List.fold_left (fun acc id ->
          let a = snd (List.find (fun (i, a) ->
            let label = assert_label_prefix ^ (string_of_int i) in
            eq_str id label) assertions_w_label)
          in
          acc @ [a]) [] unsat_core_ids
    with e ->
      let tok = Lexing.lexeme lexbuf in
      []
  in unsat_core

let get_unsat_core assertions =
  let pr = pr_list CP.string_of in
  Debug.no_1 "z3_get_unsat_core" pr pr get_unsat_core assertions

let rec imply_x (ante : Cpure.formula) (conseq : Cpure.formula) bget_cex timeout : bool =
  let input = to_smt ante (Some conseq)  bget_cex in
   (* Debug.info_hprint (add_str "z3.imply.input" pr_id) input no_pos; *)
  let () = !set_generated_prover_input input in
  let output =
    check_formula input bget_cex timeout
  in
  let () = !set_prover_original_output (String.concat "\n" output.original_output_text) in
  let res = (
      match output.sat_result with
        | Sat -> false
        | UnSat -> true
        | Unknown -> false
        | Aborted -> false
  ) in
  let () = process_stdout_print ante conseq input output res in
  res

and imply (ante : Cpure.formula) (conseq : Cpure.formula) bget_cex timeout : bool =
  let pr = CP.string_of in
  Debug.no_2(* _loop *) "smt_imply" (pr_pair pr pr) string_of_float string_of_bool
    (fun _ _-> imply_x ante conseq bget_cex timeout) (ante, conseq) timeout

let imply_ops_cex ante conseq bget_cex timeout =
  imply ante conseq bget_cex timeout
