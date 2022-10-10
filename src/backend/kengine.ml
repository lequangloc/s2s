open Globals
open Gen.Basic
open VarGen


module CF = Cformula
module CSH = Csymheap
module CP= Cpure
open Dpure


let str_normalize conj=
  let fs = CP.split_conjunctions conj in
  let wes0, re0, arith0 = List.fold_left (fun (r1,r2,r3) f ->
      if CP.is_string_form f then (r1@[f], r2, r3)
      else if CP.is_arith_form f then (r1, r2, r3@[f])
      else
        (* todo *)
        let () = print_endline "sat.engine.normalize: to check re" in
        (r1, r2@[f], r3)
  ) ([],[],[]) fs in
  let simple_wes, complex_wes = List.partition (CP.is_simple_word_equation) wes0 in
  simple_wes,  complex_wes, re0, arith0

let check_sat_str conjs =
  (* norm form:
      - word eq (complex, simple)
      - re
      - arithmetic
  *)
  let simple_wes0,  complex_wes0, re0, arith0 = List.fold_left
    (fun (r1, r2, r3, r4) f ->
        let simple_wes,  complex_wes, re, arith = str_normalize f in
        (r1@simple_wes, r2@complex_wes, r3@re, r4@arith)
    ) ([],[],[],[]) conjs in
  let res, oModel = StrSat.check_sat complex_wes0 simple_wes0 re0 arith0 Com.tree_bound_sat in
  (res, None)

let rec check_sat pdecls (f0 :CF.t) =
  let () = Debug.ninfo_hprint (add_str  "check_sat: f0" CF.string_of) f0 no_pos in
  let helper qvars fb f=
    if fb.CSH.base_heap == Cheap.HEmp then
      let vars = CP.fv fb.CSH.base_pure in
      if vars!= [] && List.for_all (fun v -> v.Var.t == String) vars then
        check_sat_str [fb.CSH.base_pure]
      else Horn.check_sat_pure pdecls fb.CSH.base_pure
    else
      if CfUtil.is_pure pdecls [] f then
        Horn.check_sat pdecls f
      else
        SlSat.check_sat pdecls f !VarGen.sat_eager_return Com.tree_bound_sat Com.tree_size_sat
  in
  let rec aux f= match f with
    | CF.Base fb -> helper [] fb f
    | CF.Exists (fb, svs) -> helper svs fb f
    | CF.Or (f1, f2, _) -> begin
        let res1, ocex1 = aux f1 in
        match res1 with
          | Out.SAT -> res1, ocex1
          | _ -> begin
              let res2, ocex2 = aux f2 in
              match res1, res2 with
                | _, Out.SAT -> res2, ocex2
                | Out.UNSAT, Out.UNSAT -> Out.UNSAT, None
                | _ -> Out.UNKNOWN, None
            end
      end
  in aux f0
