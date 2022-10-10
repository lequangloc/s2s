open VarGen
open Globals
open Printf
open Gen.Basic
open Gen.BList

type var_info = { mutable sv_info_kind : typ; id: int; }

type var_type_list = (( ident * var_info)  list)

val string_of_tlist : var_type_list -> string

val string_of_tlist_type : var_type_list * typ -> string

val string_of_tlist_type_option : var_type_list * typ option -> string

val get_type_entire : var_type_list -> typ -> typ

val get_type : var_type_list -> int -> typ

val fresh_proc_var_kind : var_type_list -> typ -> var_info

val fresh_tvar : var_type_list -> typ * var_type_list

val fresh_int_en : typ -> int

val must_unify : typ ->  typ -> var_type_list -> VarGen.loc -> var_type_list * typ

val must_unify_expect : typ ->  typ -> var_type_list -> VarGen.loc -> var_type_list * typ

val unify_expect : typ ->  typ -> var_type_list -> var_type_list * Globals.typ option

val must_unify_expect_test : typ -> typ -> var_type_list -> VarGen.loc -> typ

val unify_ptr_arithmetic : typ * 'f -> typ * 'g -> typ -> var_type_list -> VarGen.loc -> var_type_list * typ

val gather_type_info_var: Globals.ident -> var_type_list -> typ-> VarGen.loc -> var_type_list * typ

val gather_type_info_exp :  Iexp.t -> var_type_list -> typ -> var_type_list * typ

val gather_type_info_term: Irel.t list -> Iterm.t -> var_type_list -> var_type_list

val gather_type_info_pure : Irel.t list -> Ipure.t -> var_type_list -> var_type_list

val gather_type_info_heap : Inode.t list -> Ipred.t list  -> Iheap.t -> var_type_list -> var_type_list


val try_unify_data_type_args : Inode.t list -> Globals.ident -> Globals.ident -> int -> Iexp.t list -> var_type_list -> VarGen.loc -> var_type_list

val try_unify_view_type_args : Globals.ident -> Ipred.t ->  int ->  Iexp.t list -> var_type_list -> VarGen.loc -> var_type_list

val synchronize : Cformula.t -> var_type_list -> Cformula.t
