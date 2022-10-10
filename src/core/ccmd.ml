open Globals
open VarGen
open Out


module CF = Cformula

type cmd_sat = CF.t * (outcome option)

type cmd_ent = {
 ante : CF.t;
 cons : CF.t;
 expect :  (outcome option);
 bi : bool;
}

let string_of_cmd_sat (f, opt_exp)=
  let expt = match opt_exp with
    | None -> " "
    | Some r ->  "[" ^( Out.string_of r)^  "] "
  in
  "checksat" ^ expt ^ (Cformula.string_of f)  ^ "."

let string_of_cmd_ent ent=
  let expt = match ent.expect with
    | None -> " "
    | Some r ->  "[" ^( Out.string_of r)^  "," ^ (string_of_bool ent.bi) ^ "] "
  in
  "checkent" ^ expt ^ (Cformula.string_of ent.ante) ^ "\n    |= " ^
      (Cformula.string_of ent.cons)
  ^ "."
