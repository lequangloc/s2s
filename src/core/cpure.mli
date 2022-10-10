open Globals

open Term
open Exp
open Var

type formula =
  | BForm of Term.t
  | Not of formula
  | Exists of (var * formula)
  | Forall of (var * formula)
  | And of (formula * formula)
  | Or of (formula * formula)

type t = formula

type relation = (* for obtaining back results from Omega Calculator. Will see if it should be here *)
  | ConstRel of bool
  | BaseRel of (Exp.t list * t)
  | UnionRel of (relation * relation)

and constraint_rel =
  | Unknown
  | Subsumed
  | Subsuming
  | Equal
  | Contradicting

val string_of : t -> string

val string_of_relation : relation -> string

val split_conjunctions : t -> t list

val count_disj: t -> int

val join_conjunctions: t list -> VarGen.loc -> t

val join_disjunctions: t list -> t

val split_disjunctions: t -> t list

val is_string_form : t -> bool

val is_arith_form : t -> bool

val get_const_var : t -> Var.t list

val is_simple_word_equation : t -> bool

val fv : t -> Var.t list

val mkEqExp:  Exp.t -> Exp.t -> VarGen.loc -> t

val mkNeqExp:  Exp.t -> Exp.t -> VarGen.loc -> t

val mkEqZeroExp: Exp.t -> VarGen.loc -> t

val mkGteZeroExp: Exp.t -> VarGen.loc -> t

val mkGtZeroExp:  Exp.t -> VarGen.loc -> t

val mkTrue: VarGen.loc -> t

val isTrue: t -> bool

val mkFalse: VarGen.loc -> t

val isFalse: t -> bool

val mkEqVar: Var.t -> Var.t -> VarGen.loc -> t

val mkNeqVar: Var.t -> Var.t -> VarGen.loc -> t

val mkNot: t -> VarGen.loc -> t

val mkAnd : t -> t -> VarGen.loc -> t

val mkExists: Var.t list -> t -> VarGen.loc -> t

val mkForall: Var.t list -> t -> VarGen.loc -> t

val mkAnd_dumb : t -> t -> VarGen.loc -> t

val mkOr : t -> t -> VarGen.loc -> t

val equal: t -> t -> bool

val remove_redundant : t -> t
  (*remove x=x*)

val remove_primitive: (Term.t -> bool) -> t -> t

val subst_one_term: (Var.t * Exp.t) -> t -> t

val subst: (Var.t * Exp.t) list -> t -> t

val subst_var: (Var.t * Var.t) list -> t -> t

val subst_rel: (t * t) -> t -> t

val add_quantifiers: Var.t list -> t -> t

val split_quantifiers : t -> Var.t list * t

val fresh_quantifiers : t -> t

val mk_string_inv: t -> t

val drop_rel_formula_ops: unit -> (Term.t -> t option) * (Term.t -> t option)

val drop_complex_ops: unit -> (Term.t -> t option) * (Term.t -> t option)

val drop_rel_formula: t -> t

val memoise_rel_formula: Var.t list -> t -> t * (Var.t * t) list * Var.t list

val has_template_formula: t -> bool


val build_relation: (Exp.t -> Exp.t -> VarGen.loc -> Term.t) -> Exp.t list ->
  Exp.t list -> VarGen.loc -> t


val arith_simplify : t -> t

val eql_simplify : t -> t

(* decompse into pointer eq, dis and arith *)
val type_decomp : t ->  Var.t list * Var.t list * (Var.t * Var.t) list * (Var.t * Var.t) list *t

val subst_type : (typ * typ) list -> t -> t

val subtract_useless_diseq : t -> Var.t list -> t

val contain_const : t -> bool

val is_local_constraint : t -> bool * bool * bool

val contain_rel: t -> bool

val is_rel: t -> bool

val decompose_rel: t -> ident * Var.t list
