open Globals
open Gen.Basic
open VarGen

module ISH = Isymheap

type formula =
  | Base of ISH.formula
  | Exists of (ISH.formula * ((ident * primed) list))
  | Or of (formula * formula* loc)


type t = formula

val string_of: t -> string

val mkTrue : loc -> t

val mkFalse : loc -> t

val mkBase : Iheap.t -> Ipure.t -> loc -> t

val mkExists : (ident * primed) list -> Iheap.t ->
  Ipure.t -> loc -> t

val mkOr : t -> t -> loc -> t

val subst : ((ident*primed) * (ident*primed)) list -> t -> t

val apply_one : (ident*primed) * (ident*primed) -> t -> t

val rename_bound_vars : t -> t

val is_empty_heap : t -> bool

val isFalse : t -> bool
