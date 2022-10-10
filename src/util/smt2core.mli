open Globals
open Smtlib_syntax
open Smtlib_util

open Cpure
open Exp
open Var

val trans_symbol : symbol -> string

val trans_identifier : identifier -> symbol

val trans_qualidentifier : qualidentifier -> identifier

val trans_var : (pd * symbol * sort) -> Var.t

val trans_vars : (pd * symbol * sort) list -> var list

val trans_quan_var : Smtlib_syntax.sortedvar -> Var.t

val trans_quan_vars : Smtlib_syntax.sortedvar list -> var list

val trans_exp: (var list) -> specconstant -> Exp.t

val trans_term_exp: (var list) -> term -> Exp.t

val trans_formula : (var list) -> (pd * term) -> Cpure.t

val trans_formulas : (var list) -> ((pd * term) list) -> (Cpure.t list)
