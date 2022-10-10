open Globals
open VarGen

open Var

type term =
  | BConst of (bool * loc)
  | BVar of (Var.t * loc)
  | Lt of (Exp.t * Exp.t * loc)
  | Lte of (Exp.t * Exp.t * loc)
  | Gt of (Exp.t * Exp.t * loc)
  | Gte of (Exp.t * Exp.t * loc)
  | Eq of (Exp.t * Exp.t * loc) (* these two could be arithmetic or pointer or bag or list *)
  | Neq of (Exp.t * Exp.t * loc)
  | EqMax of (Exp.t * Exp.t * Exp.t * loc) (* first is max of second and third *)
  | EqMin of (Exp.t * Exp.t * Exp.t * loc) (* first is min of second and third *)
  (* bag formulas *)
  | BagIn of (Var.t * Exp.t * loc)
  | BagNotIn of (Var.t * Exp.t * loc)
  | BagSub of (Exp.t * Exp.t * loc)
  | BagMin of (Var.t * Var.t * loc)
  | BagMax of (Var.t * Var.t * loc)
  (*string logic*)
  | RelForm of (ident * (Exp.t list) * loc)

type t = term

val string_of: t -> string

val is_string_term : t -> bool

val is_arith_term : t -> bool

val is_simple_word_equation : t -> bool

val is_update_array_relation : string -> bool

val fv : t -> Var.t list

val mkEq : Exp.t -> Exp.t -> VarGen.loc -> t

val mkNeq : Exp.t -> Exp.t -> VarGen.loc -> t

val mkGt : Exp.t -> Exp.t -> VarGen.loc -> t

val mkGte : Exp.t -> Exp.t -> VarGen.loc -> t

val mkLt : Exp.t -> Exp.t -> VarGen.loc -> t

val mkLte : Exp.t -> Exp.t -> VarGen.loc -> t

val mkTrue : VarGen.loc -> t

val mkFalse : VarGen.loc -> t

val mkEqZero: Exp.t -> VarGen.loc -> t

val mkEqN: Exp.t -> int -> VarGen.loc -> t

val mkGtZero: Exp.t -> VarGen.loc -> t

val mkGteZero: Exp.t -> VarGen.loc -> t

val mkRel: string -> Var.t list ->  VarGen.loc -> t

val equalTerm :  (Var.t -> Var.t -> bool) -> t -> t -> bool

val t_subst_one_term: (Var.t * Exp.t) -> t -> t

val t_subst: (Var.t * Exp.t) list -> t -> t

val subst: (Var.t * Var.t) list -> t -> t

val is_ew_trivial_true: t -> bool -> bool

val is_ew_trivial_false: t -> bool

val head_of_string: Exp.t -> Exp.t option

val is_only_head: Exp.t -> bool

val normalize_word_eq: t -> t

val string_to_length: t -> t

val get_cconst: t -> Exp.t list

val get_const_var : t -> Var.t list

val arith_simplify : t -> t

(* decompse into pointer eq, dis and arith *)
val type_decomp : t -> Var.t list * Var.t list * (Var.t * Var.t) list * (Var.t * Var.t) list *t

val subst_type : (typ * typ) list -> t -> t

val is_local_constraint : t -> bool * bool * bool

val is_rel : t -> bool

val decompose_rel : t -> ident * Var.t list
