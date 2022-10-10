open Globals
open Gen
open VarGen

open Cpure
open Term

module PN = CpredNode

type nstatus =
  | Nopen
  | Nvalid
  | Ninvalid
  | Nunsat
  | Ncycle
  | NcycleCC
  | Nsat
  | NsatCC
  | Nincompl
  | Nreduced

type entstuck=
  | ENorm
  | ELuEmp
  | ERuEmp
  | ESDangl
  | ESNoRule
  | EPtoNoMatch
  | EBaseNoMatch

exception LPTO_DUPS_EXC
exception EARLY_SAT_DECT_EXC

let tree_size = 9192 (* 91920 -> ls 10s 9192000 -> ls_ent 42s *)
let tree_size_big = 65536
let tree_size_sat = 4096 (* 91920 6400 9192000 2097152 *)
let tree_size_sat_big = 65536
let proof_size = 9192 (*16.-3600, tree-pp-entails-tree-pp-rev.smt2.sl: 9800*)
let proof_size_big = 65536
let tree_bound = 36000 (* 360000 *)
let tree_bound_sat = 36000 (* 360000 *)
let tree_bound_sat_big = 65536
let root_parent_ID = -1

let string_of_node_status i = match i with
    | Nopen -> "open"
    | Nvalid -> "valid"
    | Ninvalid -> "invalid"
    | Nunsat -> "unsat"
    | Ncycle -> "cycle"
    | NcycleCC -> "cycleCC"
    | Nsat -> "sat"
    | NsatCC -> "satCC"
    | Nincompl -> "sat-incomplete"
    | Nreduced -> "reduced"

let string_of_entstuck e= match e with
  | ENorm -> "none"
  | ELuEmp -> "ELuEmp (valid)"
  | ERuEmp -> "ERuEmp (invalid)"
  | ESDangl -> "Stuck ESDangl"
  | ESNoRule -> "No rule"
  | EPtoNoMatch -> "pto not match"
  | EBaseNoMatch -> "TW: unfold base - LHS no match RHS"

let is_sat_fnc_x f =
  Tpdispatcher.is_sat f

let is_sat_fnc p=
  let pr1 = Cpure.string_of in
  let pr_out = string_of_bool in
  Debug.no_1 "is_sat_fnc" pr1 pr_out
      (fun _ -> is_sat_fnc_x p) p

let is_imply_x a c =
  if Cpure.isTrue c then true else
    Tpdispatcher.imply a c

let is_imply a c =
  let pr1 = Cpure.string_of in
  Debug.no_2 "Com.is_imply" pr1 pr1 string_of_bool
      (fun _ _ -> is_imply_x a c) a c

let simplify_fnc f= (* Tpdispatcher.simplify *) f

let check_sat_cpure_x ps=
  let p = List.fold_left (fun r p->
      Cpure.mkAnd r p no_pos
  ) (Cpure.mkTrue no_pos) ps in
  if is_sat_fnc p then
    (Out.SAT, [])
  else (Out.UNSAT, [])

let check_sat_cpure ps=
  let pr1 = pr_list_ln Cpure.string_of in
  let pr_out (a, _) =  Out.string_of a in
  Debug.no_1 "check_sat_cpure" pr1 pr_out
      (fun _ -> check_sat_cpure_x ps) ps
