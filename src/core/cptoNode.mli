open Globals
open Gen.Basic
open VarGen

type pto = {
    hpto_node : Var.t;
    hdata_name: ident;
    hpto_derv : bool;
    hpto_arguments : Var.t list;
    hpto_holes : int list;
    hpto_pos : loc }

type t = pto

val string_of : pto -> string

val mkPtoNode: Var.t -> Globals.ident ->  bool -> Var.t list -> int list -> loc -> pto

val subst: (Var.t * Var.t) list -> t -> t

val to_abs_pure : t list -> Var.t list * ((Var.t * Var.t) list)

val to_abs_pure_form : t list -> Cpure.t

val subst_type : (typ * typ) list -> t -> t

val equal : t -> t -> bool
