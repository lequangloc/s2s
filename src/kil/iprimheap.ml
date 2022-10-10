open Globals
open Gen.Basic

module IE = IExp

type formula = {
    node : (ident * primed);
    name : ident;
    arguments : IE.exp list;
    pos : loc }

and t = formula

let string_of f = ""
