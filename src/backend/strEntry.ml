open Globals
open Gen
open VarGen

open Cpure
open Term

open Com
open Aentry

type t = {
      ew : Term.t;
      (* ew_simpl : Term.t; *)
      re: Cpure.t list;
      arith : Cpure.t list;
      inv_arith: Cpure.t;
      model: (Var.t * Exp.t) list; (* partial assignment *)
  }

let string_of (e: t)=
  "ew = " ^ ((Term.string_of) e.ew) ^ "\n" ^
      (* "ew_simpl = " ^ (( Term.string_of) e.ew_simpl) ^ "\n" ^; *)
      "re = " ^ ((pr_list Cpure.string_of) e.re) ^ "\n" ^
      "arith = " ^ ((pr_list Cpure.string_of) e.arith) ^ "\n" ^
      "inv_arith = " ^ ((Cpure.string_of) e.inv_arith) ^ "\n" ^
      "model = " ^ ((pr_list (pr_pair Var.string_of Exp.string_of)) e.model) ^ "\n"

  let string_of_short (e: t)=
    "ew = " ^ ((Term.string_of) e.ew) ^ "\n"

(*eval e.ew *)
  let eval e=
    let () = Debug.ninfo_hprint (add_str  "Node.eval" pr_id) "" no_pos in
    let ew = e.ew in
    (* is trivially true? *)
    if Term.is_ew_trivial_true ew (not(Cpure.isTrue e.inv_arith)) then Out.SAT
    else
      (* is trivially false? *)
      if Term.is_ew_trivial_false ew then Out.UNSAT
      else
        (* is over-approximation false *)
        let tlength = Term.string_to_length ew in
        let tlength_inv = Cpure.And (Cpure.BForm tlength, e.inv_arith) in
        let () = Debug.ninfo_hprint (add_str  "tlength_inv" Cpure.string_of) tlength_inv no_pos in
        let comb = List.fold_left (fun r p ->
            Cpure.mkAnd r p no_pos
        ) tlength_inv e.arith in
        let () = Debug.ninfo_hprint (add_str  "comb" Cpure.string_of) comb no_pos in
        if not (is_sat_fnc comb) then
          Out.UNSAT
        else
          Out.UNKNOWN


class str_entry init= object
  inherit [t] aentry init as super

  method string_of () = string_of (super # get_e ())
  method string_of_short () = string_of_short (super # get_e ())
  method eval () = eval (super # get_e ())

  method get_arith () = let d = (super # get_e ()) in d.arith
  method get_inv_arith () = let d = (super # get_e ()) in d.inv_arith
  method get_ew () = let d = (super # get_e ()) in d.ew

end;;
