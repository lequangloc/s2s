open Globals
open Gen
open VarGen

open Cpure
open Term

open Com

module T = StrTree
module N = StrNode.STRNODE
module ENTRY = StrNode.STR_NODE_DATA


let check_sat_x wes wes_simpl re arith bound=
  let () = Debug.ninfo_hprint (add_str  "bound" string_of_int) bound no_pos in
  let extract_term we=
    let r = match we with
      | BForm t -> t
      | _ -> raise (Invalid_argument "s21sea.check_sat")
    in
    r
  in
  if wes==[] && wes_simpl==[] && re==[] then
    check_sat_cpure arith
  else
  let r1,we_rest = match wes with
    | [] -> begin
        match wes_simpl with
          | r::rest -> extract_term r, List.map extract_term rest
          | _ -> raise (Invalid_argument "s21sea.check_sat: no word equation")
      end
    | r::rest ->   extract_term r, List.map extract_term rest
  in
  let inv = Cpure.mk_string_inv (Cpure.BForm r1) in
  let root_data = {
      ENTRY.ew = Term.normalize_word_eq r1;
      ENTRY.ew_wait = we_rest;
      ENTRY.ew_done = [];
      (* N.ENTRY.ew_simpl = extract_term wes_simpl; *)
      ENTRY.re =  re;
      ENTRY.arith = arith;
      ENTRY.inv_arith = inv;
      ENTRY.model = [];
  } in
  let root = {
      N.id = root_parent_ID+1;
      N.data = root_data;
      N.parent = root_parent_ID;
      N.child = [];
      N.height = 0;
      N.status = Nopen;
  } in

  let t = new T.cyclic root bound in
  let () = t # build_proof () in
  (* let s = t # string_of () in *)
  (* let () = print_endline s in *)
  let () = Debug.ninfo_hprint(add_str "\nTREE:\n" (pr_id)) ( t # string_of ()) no_pos in

  let res, models = t#find_satisfiability () in
  if  res == Out.UNSAT then (res, [])
  else
    (* extend tree with re *)
    let interested_svl0 = List.fold_left (fun r p ->
        r@(Cpure.fv p)) [] root.N.data.ENTRY.arith in
    let interested_svl1 = Var.remove_dups interested_svl0 in
    let interested_svl2 = List.fold_left (fun r isv ->
        try
          let sid = lookup_svar_from_ivar isv.Var.id in
          let string_sv = {Var.id = sid;
          Var.t = String;
          Var.p = isv.Var.p
          } in
          r@[string_sv]
        with Not_found -> r
    ) [] interested_svl1 in
    let () = Debug.ninfo_hprint(add_str "\nroot.N.data.N.ENTRY.arith:\n" (pr_list Cpure.string_of)) root.N.data.ENTRY.arith no_pos in
    let () = Debug.ninfo_hprint(add_str "\ninterested_svl0:\n" (pr_list  Var.string_of)) interested_svl0 no_pos in
    let () = Debug.ninfo_hprint(add_str "\ninterested_svl1:\n" (pr_list  Var.string_of)) interested_svl1 no_pos in
    let () = Debug.ninfo_hprint(add_str "\ninterested_svl2:\n" (pr_list  Var.string_of)) interested_svl2 no_pos in
    if root.N.data.ENTRY.arith == [] || interested_svl2==[] then (res, [])
    else
      Cfg.check_sat_parikh t models root.N.data.ENTRY.arith interested_svl2


let check_sat wes wes_simpl re arith bound=
  let pr1 = pr_list Cpure.string_of in
  let pr2 = pr_list (pr_pair Var.string_of Exp.string_of) in
  let pr3 = pr_pair Out.string_of pr2 in
  Debug.no_5 "s2str.check_sat" pr1 pr1 pr1
      pr1 string_of_int pr3
      (fun _ _ _ _ _ -> check_sat_x wes wes_simpl re arith bound)
      wes wes_simpl re arith bound
