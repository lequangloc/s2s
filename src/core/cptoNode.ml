open Globals
open Gen.Basic
open VarGen

module CP = Cpure

type pto = {
    hpto_node : Var.t;
    hdata_name: ident;
    hpto_derv : bool;
    hpto_arguments : Var.t list;
    hpto_holes : int list;
    hpto_pos : loc }

type t = pto

let string_of h =
  ((Var.string_of h.hpto_node) ^ "::" ^ h.hdata_name ^
       ((pr_list_angle Var.string_of) h.hpto_arguments) )

let mkPtoNode c id dr args holes l={
    hpto_node = c;
    hdata_name = id;
    hpto_derv = dr;
    hpto_arguments = args;
    hpto_holes = holes;
    hpto_pos = l }


let subst sst pto=
  { pto with hpto_node = Var.subst_var_par sst pto.hpto_node;
      hpto_arguments = List.map (Var.subst_var_par sst) pto.hpto_arguments;
  }

let subst_type t_sst pto=
  { pto with hpto_node = Var.subst_type t_sst pto.hpto_node;
      hpto_arguments = List.map (Var.subst_type t_sst) pto.hpto_arguments;
  }

let to_abs_pure (ptos: t list): Var.t list * ((Var.t * Var.t) list)=
  let rec helper svs res= match svs with
    | sv::rest ->
          let neqs = List.map (fun sv1 -> (sv, sv1)) rest in
          helper rest (res@neqs)
    | [] -> res
  in
  (* not eq null *)
  let neq_null_svs = List.map (fun n-> n.hpto_node) ptos in
  (* pairwaise not eq *)
  let neqs = helper neq_null_svs [] in
  (neq_null_svs, neqs)

let to_abs_pure_form (ptos: t list): Cpure.t=
  let rec helper svs res= match svs with
    | sv1::rest ->
          let neq = List.fold_left (fun acc_p sv2 ->
              let p = CP.mkNeqExp (Exp.mkVar sv1 no_pos) (Exp.mkVar sv2 no_pos) no_pos in
              CP.mkAnd acc_p p no_pos
          ) res rest in
          helper rest neq
    | [] -> res
  in
  let eNull = Exp.Null no_pos in
  (* not eq null *)
  let f1 = List.fold_left (fun acc_p n ->
        let p = CP.mkNeqExp (Exp.mkVar n.hpto_node no_pos) eNull no_pos in
        CP.mkAnd acc_p p no_pos
    ) (CP.mkTrue no_pos) ptos in
  (* pairwaise not eq *)
  let f2 = helper (List.map (fun n -> n.hpto_node) ptos) f1 in
  f2

let equal n1 n2=
  Ustr.str_eq n1.hdata_name n2.hdata_name &&
      Var.equal n1.hpto_node n2.hpto_node &&
      List.for_all (fun (sv1, sv2) -> Var.equal sv1 sv2)
      (List.combine n1.hpto_arguments n2.hpto_arguments)
