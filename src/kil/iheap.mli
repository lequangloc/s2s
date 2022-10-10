
open Globals
open Gen.Basic
open VarGen

type formula =
  | Star of (formula * formula * loc)
  | PtoNode of IheapNode.pto
  | HeapNode2 of IheapNode.heap2
  | PredNode of IheapNode.hpred
  | HEmp
  | HTrue
  | HFalse


and t = formula

val string_of: t -> string

val mkHTrue : loc -> t

val mkHFalse : loc -> t

val mkPtoNode: (Globals.ident * VarGen.primed) ->
  Globals.ident -> int -> bool -> (Iexp.t list) -> loc -> t

val mkHeapNode2: (Globals.ident * VarGen.primed) -> Globals.ident -> int
  -> bool -> (Globals.ident * Iexp.t) list -> loc -> t

val mkPredNode: Globals.ident -> int -> bool -> Iexp.t list -> loc -> t

val mkStar: t -> t -> loc -> t

val h_apply_one : (ident*primed) * (ident*primed) -> t -> t

val get_anon_var : t -> (ident * primed) list
