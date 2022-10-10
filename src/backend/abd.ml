
open Globals
open VarGen
open Gen

module CP = Cpure

(* let imply = Tpdispatcher.imply *)

let arith_abduce_x cur_ass ante conse=
  if CP.isTrue conse then
    true, []
  else
    let r = Com.is_imply ante conse in
    if r then
      true, []
    else
      if CP.contain_rel ante then
        (* under-approximate LHS and check invalid *)
        try
          let (b, r) = List.find (fun (_, h) -> Cpure.is_rel h) cur_ass in
          (*subst*)
          let ante1 = Cpure.subst_rel (b, r) ante in
          let r = Com.is_imply ante1 conse in
          if not r then
            false, []
          else
            true, [(ante, conse)]
        with Not_found ->
            true, [(ante, conse)]
      else r, []

let arith_abduce cur_ass ante conse=
  let pr1 = CP.string_of in
  let pr2 = pr_list_ln (pr_pair pr1 pr1) in
  Debug.no_3 "arith_abduce" pr2 pr1 pr1
      (pr_pair string_of_bool pr2)
      (fun _ _  _ -> arith_abduce_x cur_ass ante conse)
      cur_ass ante conse

let arith_sat_id f = false, []

let arith_sat_abduce_x f =
  if CP.contain_rel f then
    true, [(f, CP.mkFalse no_pos)]
  else
    false, []

let arith_sat_abduce f=
  let pr1 = CP.string_of in
  let pr2 = pr_pair pr1 pr1 in
  let pr_out = pr_pair string_of_bool (pr_list_ln pr2) in
  Debug.no_1 "arith_sat_abduce" pr1 pr_out
      (fun _ -> arith_sat_abduce_x f) f

