open Globals
open Gen.Basic
open VarGen

module CP = Cpure
module CH = Cheap


type formula = {
  base_heap : CH.t;
  base_pure : CP.t;
  base_pos : loc }

type t = formula

let string_of f = (CH.string_of f.base_heap) ^ " & " ^ (CP.string_of f.base_pure)


let mk h p l =  {
  base_heap = h;
  base_pure = p ;
  base_pos = l }

let mkTrue p = {
    base_heap = CH.mkHTrue p;
    base_pure = CP.mkTrue p;
    base_pos = p;
}

let mkFalse p = {
    base_heap = CH.mkHTrue p;
    base_pure = CP.mkFalse p;
    base_pos = p;
}

let isFalse p = CP.isFalse p.base_pure

let mkStarAnd f1 f2= {
    base_heap = CH.mkStarAnd f1.base_heap f2.base_heap f1.base_pos;
    base_pure = CP.mkAnd f1.base_pure f2.base_pure f1.base_pos;
    base_pos = f1.base_pos
}


let subst sst f= { f with base_heap = CH.h_subst sst f.base_heap;
    base_pure = CP.subst_var sst f.base_pure;
}

let subst_type t_sst f= { f with base_heap = CH.subst_type t_sst f.base_heap;
    base_pure = CP.subst_type t_sst f.base_pure;
}

let subst_view_inv pred_invs f0=
  let nh, ps = CH.subst_view_inv pred_invs f0.base_heap in
  let p = CP.join_conjunctions (f0.base_pure::ps) (f0.base_pos) in
  {f0 with base_heap = nh;
      base_pure = p;
  }

let fv b= Var.remove_dups ((CH.fv b.base_heap)@(CP.fv b.base_pure))

let sequentialize_views sh = {sh with base_heap = CH.sequentialize_views sh.base_heap}

let subtract_pto fb pto=
  {fb with base_heap = CH.subtract_pto fb.base_heap pto}

let subtract_pred fb vn=
  {fb with base_heap = CH.subtract_pred fb.base_heap vn}

let equal_x fb1 fb2=
  if CP.equal fb1.base_pure fb2.base_pure then
    CH.equal fb1.base_heap fb2.base_heap
  else false

let equal f1 f2=
  let pr1 = string_of in
  Debug.no_2 "CB.equal" pr1 pr1 string_of_bool
      (fun _ _ -> equal_x f1 f2) f1 f2
