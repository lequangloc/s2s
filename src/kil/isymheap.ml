open Globals
open Gen.Basic
open VarGen

module IP = Ipure
module IH = Iheap


type formula = {
  base_heap : IH.t;
  base_pure : IP.t;
  base_pos : loc }

type t = formula

let string_of f = (IH.string_of f.base_heap) ^ " & " ^ (IP.string_of f.base_pure)


let mk h p l =  {
  base_heap = h;
  base_pure = p ;
  base_pos = l }

let mkTrue p = {
    base_heap = IH.mkHTrue p;
    base_pure = IP.mkTrue p;
    base_pos = p;
}

let mkFalse p = {
    base_heap = IH.mkHTrue p;
    base_pure = IP.mkFalse p;
    base_pos = p;
}

let rec apply_one ((fr, t) as s : ((ident*primed) * (ident*primed))) (fb : t) =
  {fb with
      base_heap = IH.h_apply_one s fb.base_heap;
      base_pure = IP.apply_one s fb.base_pure;
  }

let rec subst sst (f : t) = match sst with
  | s :: rest -> subst rest (apply_one s f)
  | [] -> f
