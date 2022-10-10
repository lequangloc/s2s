open Globals
open Gen.Basic
open VarGen

module IE = Iexp

type formula = {
    node : (ident * primed);
    name : ident;
    arguments : IE.exp list;
    pos : loc }

and t = formula

val string_of: t -> string
