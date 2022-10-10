open Globals
open Gen.Basic

module IE = IExp

type formula = { h_formula_heap_node : (ident * primed);
                       h_formula_heap_name : ident;
                       h_formula_heap_arguments : IE.exp list;
                       h_formula_heap_pos : loc }

and t = formula

val string_of: t -> string
