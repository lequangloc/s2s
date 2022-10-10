open Globals
open Gen.Basic
open VarGen

type hpred = {
    hpred_name : ident;
    hpred_derv : bool;
    hpred_arguments : Var.t list;

    (* for sat/ent cyclic proofs *)
    hpred_unfold_num : int;
    hpred_unfold_seq : int;
    mutable hpred_unfold_step : int;

    (*rhs quantifier instantiated*)
    hpred_rhs_inst: bool;
    hpred_pos : loc }

and t = hpred

let string_of_short h= (h.hpred_name ^
       ((pr_list_round  Var.string_of) h.hpred_arguments) )

let string_of h= h.hpred_name ^
       ((pr_list_round  Var.string_of) h.hpred_arguments) ^
       "_"^(string_of_int h.hpred_unfold_num) ^
       "(+"^(string_of_int h.hpred_unfold_step) ^ ")"^
       "^"^(string_of_int h.hpred_unfold_seq)^"(" ^ (string_of_bool h.hpred_rhs_inst) ^ ")"



let mk ?un:(un=0) ?us:(us=(-1)) ?ut:(ut=1) ?inst:(it=true) id dr hl l ={
    hpred_name = id;
    hpred_derv = dr;
    hpred_arguments = hl;
    hpred_unfold_num=un;
    hpred_unfold_seq=us;
    hpred_unfold_step = ut;
    hpred_rhs_inst = it;
    hpred_pos = l }


let subst sst p=
  { p with
      hpred_arguments = List.map (Var.subst_var_par sst) p.hpred_arguments;
  }

let subst_type t_sst p=
  { p with
      hpred_arguments = List.map (Var.subst_type t_sst) p.hpred_arguments;
  }

let bfs_cmp p1 p2 : int=
  if p1.hpred_unfold_num < p2.hpred_unfold_num then -1
  else if p1.hpred_unfold_num > p2.hpred_unfold_num then 1
  else begin
    if p1.hpred_unfold_seq < p2.hpred_unfold_seq then -1
    else if p1.hpred_unfold_seq > p2.hpred_unfold_seq then 1
    else 0
  end


let equal n1 n2=
  Ustr.str_eq n1.hpred_name n2.hpred_name &&
      List.for_all (fun (sv1, sv2) -> Var.equal sv1 sv2)
      (List.combine n1.hpred_arguments n2.hpred_arguments)


