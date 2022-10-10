
open Globals
open Gen
open VarGen

module PN = CpredNode

type nstatus =
  | Nopen
  | Nvalid | Ninvalid
  | Nunsat
  | Ncycle | NcycleCC
  | Nsat
  | NsatCC (* all inductive predicates are ex quantified. *)
  | Nincompl
  | Nreduced

type entstuck=
  | ENorm
  | ELuEmp | ERuEmp
  | ESDangl
  | ESNoRule
  | EPtoNoMatch
  | EBaseNoMatch

exception LPTO_DUPS_EXC
exception EARLY_SAT_DECT_EXC

val tree_size : int
val tree_size_big : int
val tree_size_sat : int
val tree_size_sat_big : int
val proof_size : int
val proof_size_big : int
val tree_bound : int
val tree_bound_sat : int
val tree_bound_sat_big : int
val root_parent_ID : int

val string_of_node_status : nstatus -> ident

val string_of_entstuck: entstuck -> ident

val is_sat_fnc : (*?eq:bool ->*) Cpure.t -> bool

val is_imply : (*?eq:bool ->*) Cpure.t -> Cpure.t -> bool

val simplify_fnc : Cpure.t ->  Cpure.t

val check_sat_cpure : Cpure.t list -> Out.outcome * 'a list
