open Globals
open Gen.Basic
open VarGen


type term=
  | BConst of (bool * loc)
  | BVar of ((ident * primed) * loc)
  | Lt of (Iexp.t * Iexp.t * loc)
  | Lte of (Iexp.t * Iexp.t * loc)
  | Gt of (Iexp.t * Iexp.t * loc)
  | Gte of (Iexp.t * Iexp.t * loc)
(* these two could be arithmetic or pointer or bags or lists *)
  | Eq of (Iexp.t * Iexp.t * loc)
  | Neq of (Iexp.t * Iexp.t * loc)
  | EqMax of (Iexp.t * Iexp.t * Iexp.t * loc) (* first is max of second and third *)
  | EqMin of (Iexp.t * Iexp.t * Iexp.t * loc) (* first is min of second and third *)
  (* bags and bag formulae *)
  | BagIn of ((ident * primed) * Iexp.t * loc)
  | BagNotIn of ((ident * primed) * Iexp.t * loc)
  | BagSub of (Iexp.t * Iexp.t * loc)
  | BagMin of ((ident * primed) * (ident * primed) * loc)
  | BagMax of ((ident * primed) * (ident * primed) * loc)
(*Relational formula to capture relations, for instance, s(a,b,c) or t(x+1,y+2,z+3), etc. *)
  | RelForm of (ident * (Iexp.t list) * loc)

type t = term

val string_of : t -> string

val mkTrue : loc -> t

val mkFalse : loc -> t

val isConstTrue : t -> bool

val isConstFalse : t -> bool

val mkBVar: ( Globals.ident * VarGen.primed) -> loc -> t

val mkLt: Iexp.t -> Iexp.t -> loc -> t

val mkLte: Iexp.t -> Iexp.t -> loc -> t

val mkGt: Iexp.t -> Iexp.t -> loc -> t

val mkGte: Iexp.t -> Iexp.t -> loc -> t

val mkEq: Iexp.t -> Iexp.t -> loc -> t

val mkNeq: Iexp.t -> Iexp.t -> loc -> t

val mkEqMax: Iexp.t -> Iexp.t -> Iexp.t -> loc -> t

val mkEqMin: Iexp.t -> Iexp.t -> Iexp.t -> loc -> t

val mkBagIn: (ident * primed) -> Iexp.t -> loc -> t

val mkBagNotIn: (ident * primed) -> Iexp.t -> loc -> t

val mkBagSub: Iexp.t -> Iexp.t -> loc -> t

val mkBagMin: (ident * primed) -> (ident * primed) -> loc -> t

val mkBagMax: (ident * primed) -> (ident * primed) -> loc -> t

val mkRelForm: ident -> (Iexp.t list) -> loc -> t

val fv : t -> (Globals.ident * VarGen.primed) list

val apply_one : (ident*primed) * (ident*primed) -> t -> t
