open Globals
open Gen
open VarGen

open Cpure
open Term

open Com

module STR_NODE_DATA = struct
  type t = {
      mutable ew : Term.t;
      mutable ew_wait: Term.t list;
      mutable ew_done: Term.t list;
      (* ew_simpl : Term.t; *)
      re: Cpure.t list;
      arith : Cpure.t list;
      inv_arith: Cpure.t;
      model: (Var.t * Exp.t) list; (* partial assignment *)
  }

  let string_of (e: t)=
    "ew = " ^ ((Term.string_of) e.ew) ^ "\n" ^
    "ew_wait = " ^ ((pr_list Term.string_of) e.ew_wait) ^ "\n" ^
    "ew_done = " ^ ((pr_list Term.string_of) e.ew_done) ^ "\n" ^
    (* "ew_simpl = " ^ (( Term.string_of) e.ew_simpl) ^ "\n" ^; *)
        "re = " ^ ((pr_list Cpure.string_of) e.re) ^ "\n" ^
        "arith = " ^ ((pr_list Cpure.string_of) e.arith) ^ "\n" ^
        "inv_arith = " ^ ((Cpure.string_of) e.inv_arith) ^ "\n" ^
        "model = " ^ ((pr_list (pr_pair Var.string_of Exp.string_of)) e.model) ^ "\n"

  let string_of_short (e: t)=
    "ew = " ^ ((Term.string_of) e.ew) ^ "\n"

(*eval e.ew *)
  let eval _ _ _ e=
    let () = Debug.ninfo_hprint (add_str  "Node.eval" pr_id) "" no_pos in
    let ew = e.ew in
    (* is trivially true? *)
    if Term.is_ew_trivial_true ew (not(Cpure.isTrue e.inv_arith)) then
      if !mul_eq_words then begin
        let () = e.ew_done <- e.ew_done@[e.ew] in
        match e.ew_wait with
          | [] -> Out.SAT, []
          | x::rest -> begin
              let () = e.ew <- x in
              let () = e.ew_wait <- rest in
              Out.UNKNOWN, []
            end
      end
      else
        Out.SAT, []
    else
      (* is trivially false? *)
      if Term.is_ew_trivial_false ew then Out.UNSAT, []
      else
        (* is over-approximation false *)
        let tlength = Term.string_to_length ew in
        let tlength_inv = Cpure.And (Cpure.BForm tlength, e.inv_arith) in
        let () = Debug.ninfo_hprint (add_str "tlength_inv" Cpure.string_of) tlength_inv no_pos in
        let comb = List.fold_left (fun r p ->
            Cpure.mkAnd r p no_pos
        ) tlength_inv e.arith in
        let () = Debug.ninfo_hprint (add_str "comb" Cpure.string_of) comb no_pos in
        if not (is_sat_fnc comb) then
          Out.UNSAT, []
        else
          Out.UNKNOWN, []

   let eval_all a e= fst (eval [] a [] e)


end;;


module STRNODE = Node.FNode(STR_NODE_DATA)
