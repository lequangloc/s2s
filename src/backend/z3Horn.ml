
(*Z3 Horn requires z3.4.6 *)
(* *)
(* *)

open Globals
open Gen.Basic
open VarGen

open Z3

module CF = Cformula
module CSH = Csymheap
module CFU = CfUtil
module CPeN = CpredNode
module CP = Cpure

let smt_string_of_form uvars f=
  let smt_of_ext_formula fb=
    let spure = smt_of_formula fb.CSH.base_pure in
    let views, _ = Cheap.star_decompose fb.CSH.base_heap in
    List.fold_left (fun sacc view ->
        let smt_of_pure_view =  "(" ^ (view.CPeN.hpred_name) ^ " " ^
          (String.concat " " (List.map Var.string_of view.CPeN.hpred_arguments)) ^ ")" in
        "(and " ^ smt_of_pure_view ^ " " ^ sacc ^ ")"
    ) spure views
  in
  match f with
    | CF.Base fb -> (smt_of_ext_formula fb, [])
    | CF.Exists (fb, qvars) ->
          (* replace qvars by uvars, if possible: v= x-1 ==> x=v+1 *)
          let fr_qvars = Var.fresh_vars qvars in
          let sst = List.combine qvars fr_qvars in
          let fb1 = CSH.subst sst fb in
          (smt_of_ext_formula fb1, fr_qvars)
    | _ -> Gen.report_error no_pos "Horn.z3_string_of_form: disjunction is not allowed"


(* local function
(*  input: pred p (v1,v2) == f1 \/ f2     *)
(*  output: (declare-rel p(Type1 Type2))  *)
(*          (rule (=> f1 p(v1, v2)))      *)
(*          (rule (=> f2 p(v1, v2)))      *)
(*          a set of variables v1, v2,... *)
*)
let smt_string_of_pred_x (pn: string) (args: Var.t list) (f: CF.t)=
  let disjs = CF.list_of_disjuncts f in
  let decl = "(declare-rel " ^ pn ^ " (" ^ (String.concat " "
      (List.map (fun v -> string_of_typ (Var.type_of v)) args)) ^ "))\n" in
  let head = "(" ^ pn ^ " " ^ (String.concat " " (List.map Var.string_of args)) ^ ")" in
  let rules, vars = List.fold_left (fun (acc1,acc2) f ->
      let body,vars = smt_string_of_form args f in
     acc1@["(rule (=> " ^ body ^ " "^ head ^ "))\n"], acc2@vars
  ) ([],[]) disjs in
  decl,rules, vars

let smt_string_of_pred (pn: string) (args: Var.t list) (f: CF.t)=
  Debug.no_3 "z3Horn.smt_string_of_pred" pr_id (pr_list Var.string_of) CF.string_of
      (pr_triple pr_id (pr_list_ln pr_id) (pr_list Var.string_of))
      (fun _ _ _ -> smt_string_of_pred_x pn args f) pn args f

let is_sat_chc_catch smt_f bget_cex timeout=
  try
    let output = (
        check_formula smt_f bget_cex timeout
    ) in
    let res = match output.sat_result with
      | UnSat -> Out.UNSAT
      | Sat -> Out.SAT
      | _ -> Out.UNKNOWN in
    res
  with Illegal_Prover_Format s ->
      print_endline_quiet ("\nWARNING : Illegal_Prover_Format for :"^s);
      print_endline_quiet ("Apply z3.is_sat_chc on formula :"^(smt_f));
      flush stdout;
      (* failwith s *)
      Out.UNKNOWN

let smt_var_decl v=
  "(declare-var " ^ (smt_of_var v) ^ " " ^ (string_of_typ v.Var.t) ^ ")\n"

let smt_var_decls fvars = String.concat "" (List.map  smt_var_decl fvars)

let is_sat_chc pdecls f sat_no=
   (* find all predicates from f *)
  let all_pn = CFU.get_closure_preds pdecls [f] [] in
  (* to Horn clauses *)
  let smt_pred_decls, smt_rules, qvars, uvars =
    List.fold_left ( fun (acc1, acc2, acc3, acc4) pdecl ->
        let e_decls, e_rules, e_vars = smt_string_of_pred pdecl.Cpred.pred_name
          pdecl.Cpred.pred_vars pdecl.Cpred.pred_formula in
        (acc1@[e_decls], acc2@e_rules, acc3@e_vars, acc4@pdecl.Cpred.pred_vars)
    ) ([],[],[], []) all_pn in
  (* query rule *)
  let uvars0 = CF.fv f in
  let q_body, qvars0 = smt_string_of_form uvars0 f in
  let q_pred = (fresh_any_name "Q") in
  let vars0 = (uvars0@qvars0) in
  let q_decl = "(declare-rel " ^ q_pred ^ " (" ^ (String.concat " " (List.map (fun v-> string_of_typ (Var.type_of v)) vars0)) ^ "))\n" in
  let q_head = "(" ^ q_pred ^ " " ^  (String.concat " " (List.map Var.string_of vars0)) ^ ")" in
  let q_rule = "(rule (=> " ^ q_body ^ q_head ^ "))\n" in
  (* declare vars *)
  let smt_var_decls = smt_var_decls (List.filter (fun sv -> not (Var.is_rel_typ sv)) (Var.remove_dups (qvars@uvars@vars0))) in
  (* call z3: set-option :fixedpoint.engine datalog *)
  let smt_query = "(query " ^ q_pred ^ " )" in
  let smt_f =   smt_var_decls ^
      (String.concat "\n" (smt_pred_decls@smt_rules@[q_decl;q_rule;smt_query])) in
  let () = Debug.info_hprint (add_str "smt_f" pr_id) smt_f no_pos in
  is_sat_chc_catch smt_f false z3_sat_timeout_limit
