
open Globals
open Gen.Basic
open VarGen


type formula =
  | BForm of Iterm.t
  | And of (formula * formula * loc)
  | Or of (formula * formula * loc)
  | Not of (formula * loc)
  | Forall of ((ident * primed) * formula * loc)
  | Exists of (( ident * primed) * formula * loc)

and t = formula

val string_of : t -> string

val mkTrue : loc -> t

val mkFalse : loc -> t

val mkBForm: Iterm.t -> t

val mkAnd : t -> t -> loc -> t

val mkOr : t -> t -> loc -> t

val mkNot : t -> loc -> t

val mkForall : (ident * primed) list -> t -> loc -> t

val mkExists : (ident * primed) list -> t -> loc -> t

val isConstTrue : t -> bool

val isConstFalse : t -> bool

val fv : t -> (Globals.ident * VarGen.primed) list

val subst : ((ident*primed) * (ident*primed)) list -> t -> t

val apply_one : (ident*primed) * (ident*primed) -> t -> t
