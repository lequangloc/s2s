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


let string_of e = match e with
  | VALID -> "unsat"
  | INVALID -> "sat"
  | UNKNOWN -> "unknown"
  | SAT -> "sat"
  | SATCM -> "sat (conditionally combined)"
  | UNSAT -> "unsat"
  | NONTERM -> "nontern"

let validate e o=
  if e==o then (true, "")
  else (false, "Expect " ^ (string_of e) ^", got " ^ (string_of o))
