(*
this module handles (dis)eq logic
*)

open Globals
open Gen
open VarGen


module CP = Cpure
module CT = Term
module E = Exp
module V = Var

type t = {
    qvars : V.t list;
    eqs : (V.t * V.t) list;
    diseqs : (V.t * V.t) list;
    null_vars : V.t list;
    disnull_vars : V.t list;
    is_poss_sat : bool;
}

val string_of_eq : (V.t * V.t) -> string

val string_of_eqs : (V.t * V.t) list -> string

val string_of_diseq  : (V.t * V.t) -> string

val string_of_diseqs : (V.t * V.t) list -> string

val string_of_null_vars: V.t list -> string

val string_of_disnull_vars: V.t list -> string

val string_of : t -> string

val eq : t -> t -> bool

val fv : t -> V.t list

val subst: (V.t * V.t) list -> t -> t

val mk_diseq: V.t * V.t -> bool * (V.t * V.t)

val mk_diseqs: (V.t * V.t) list -> bool * ((V.t * V.t) list)

val elim_ex_qvars: V.t list -> t -> V.t list * t

val elim_eq: t -> ((V.t * V.t) list * V.t list * (V.t * V.t) list * t)

val mk : V.t list -> V.t list -> V.t list -> (V.t * V.t) list -> (V.t * V.t) list -> t

val mkFalse : unit -> t

val mkAnd_eqs : t ->  (V.t * V.t) list -> t

val mkAnd_diseqs : t ->  (V.t * V.t) list -> t

val mkAnd_disnull : t ->  V.t list -> t

val subst_one : (V.t * V.t) -> t -> t

val remove_dups : t -> t

val check_sat : t -> Out.t

val is_top: t -> bool

val check_sat_over : t -> Out.t

val to_pure : t -> CP.t

val decompose : t -> V.t list * V.t list * ((V.t * V.t) list) * ((V.t * V.t) list)

val mkAnd : t -> t -> t

(* hypothesis: subtract for the second from the frist.
 ret the new second *)
val hypo: t -> t -> t

val elim_ex_null_var: t -> V.t list * (V.t * V.t) list * t

(* val ex_null: t -> t *)

val  expand_closure: t -> t
