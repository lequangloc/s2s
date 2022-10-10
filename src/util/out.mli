open Globals
open VarGen


type outcome =
  | VALID
  | INVALID
  | UNKNOWN
  | SAT
  | SATCM
  | UNSAT
  | NONTERM

type t = outcome

val string_of: t -> string

val validate : t -> t -> bool * string
