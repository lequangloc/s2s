open Globals
open Gen.Basic
open VarGen


type pto = {
    heap_node : (ident * primed);
    heap_name : ident;
    heap_deref : int;
    heap_derv : bool;
    heap_arguments : Iexp.t list;
    heap_pos : loc }

and heap2 = {
    heap2_node : (ident * primed);
    heap2_name : ident;
    heap2_deref : int;
    heap2_derv : bool;
    heap2_arguments : (ident * Iexp.t) list;
    heap2_pos : loc }

and hpred = {
    (* heap2_node : (ident * primed); *)
    hpred_name : ident;
    hpred_deref : int;
    hpred_derv : bool;
    hpred_arguments : Iexp.t list;
    hpred_pos : loc }

val string_of_pto : pto -> string

val string_of_heap2 : heap2 -> string

val string_of_hpred : hpred -> string

val mkPtoNode: (Globals.ident * VarGen.primed) -> Globals.ident -> int -> bool -> Iexp.t list -> loc -> pto

val mkNode2: (Globals.ident * VarGen.primed) -> Globals.ident -> int -> bool -> (Globals.ident * Iexp.t) list -> loc -> heap2

val mkPredNode: Globals.ident -> int -> bool -> Iexp.t list -> loc -> hpred

val node2_to_pto : Inode.t list -> heap2 -> pto
