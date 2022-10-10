open Globals
open VarGen

(* spec var *)
type var = {
    t : typ ;
    id:  ident;
    p: primed;
}

type t = var

type pair = t * t

val null_var : t

val mk : typ -> ident -> primed -> t

val mk_unprimed : typ -> ident ->  t

val compare : t -> t -> int

val equal : t -> t -> bool

val equal_pair_vars : (t * t) -> (t*t)-> bool

val string_of : t -> string

val string_of_pair : t * t -> string

val string_of_full : t -> string

val string_of_list : t list -> string

val string_of_full_list : t list -> string

val name_of : t -> string

val type_of : t -> typ

val is_primed : t -> bool

val is_rel_typ : t -> bool

val is_node : t -> bool

val is_arr_typ : t -> bool

val is_inter_deference_spec_var : t -> bool

val remove_dups : t list -> t list

val intersect: t list -> t list -> t list

val diff: t list -> t list -> t list

val mem : t -> t list -> bool

val fresh_var: t -> t

val fresh_vars: t list -> t list

val subst: (t * t) list -> t -> t

val subst_var_par: (t * t) list -> t -> t

val lookup_length_var_of_string: t -> t

val null_var : t

val subst_type : (typ * typ) list -> t -> t

(* val eq_closure : (t * t) list -> t list -> t list *)

val get_eq_closure : (t * t) list -> t list -> t list
(* get closure of a list of vars *)

val to_parallel_subst: (t*t) list -> (t*t) list
