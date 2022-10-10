open Globals
open Gen.Basic
open VarGen


module IP = Ipure
module IH = Iheap

type formula = {
  base_heap : IH.formula;
  base_pure : IP.formula;
  base_pos : loc }

type t = formula

val string_of: t -> string

val mk :  Iheap.t -> Ipure.t -> loc -> t

val mkTrue : loc -> t

val mkFalse : loc -> t

val subst : ((ident*primed) * (ident*primed)) list -> t -> t

val apply_one : (ident*primed) * (ident*primed) -> t -> t
