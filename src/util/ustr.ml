open Globals
open Gen

let string_of_ident_list l = "["^(String.concat "," l)^"]"

let str_eq s1 s2 = String.compare s1 s2 = 0
