open Globals
open VarGen
open Var

type exp =
  | Null of loc
  | Var of (Var.t * loc)
  | IConst of (int * loc)
  | FConst of (float * loc)
  | SConst of (ident * loc)
  | CConst of (int * loc)
  | Add of (exp * exp * loc)
  | Subtract of (exp * exp * loc)
  | Mult of (exp * exp * loc)
  | Div of (exp * exp * loc)
  | Max of (exp * exp * loc)
  | Min of (exp * exp * loc)
  | TypeCast of (typ * exp * loc)
        (* bag expressions *)
  | Bag of (exp list * loc)
  | BagUnion of (exp list * loc)
  | BagIntersect of (exp list * loc)
  | BagDiff of (exp * exp * loc)
  | ArrayAt of (Var.t * (exp list) * loc)
        (*String expressions*)
  | Concat of (exp * exp * loc)

type t = exp

val is_concat : t -> bool

val string_of : t -> string

val is_string_exp : t -> bool

val is_arith_exp : t -> bool

val is_string_var: t -> bool

val is_string_const : t -> bool

val is_null : t -> bool

val is_one : t -> bool

val is_zero : t -> bool

val combine_avars : t -> t -> Var.t list

val fv : ?dups:bool -> t -> Var.t list

val afv_list: t list -> Var.t list

val mkVar: Var.t -> loc -> t

val mkIConst : int -> VarGen.loc -> t

val mkCConst : int -> VarGen.loc -> t

val mkEmpCConst : VarGen.loc -> t

val isEmpCConst :  t -> bool

val mkConcatExp: t -> t -> VarGen.loc -> t

val eqExp_f :  (Var.t -> Var.t -> bool) -> t -> t -> bool

val eqExp_list_f : (Var.t -> Var.t -> bool)  -> t list -> t list -> bool

val subst_one_term: (Var.t * t) -> t -> t

val subst: (Var.t * Var.t) list -> t -> t

val flatten_concat: t -> t list -> t list

val combine_concat: t -> t list -> VarGen.loc -> t

val normalize_concat: t -> t

val string_to_length: t -> t

val mkZero: VarGen.loc -> t

val mkN: int -> VarGen.loc -> t

val get_cconst: t -> t list

val mkAdd_list: t list -> VarGen.loc -> t

val purge_mult : t -> t

val simp_mult : t -> t

val split_sums  : t -> ( t option) * (t option)

val move_lr : t option -> t option -> t option -> t option -> VarGen.loc ->  t * t

val move_lr3 : t option -> t option -> t option -> t option -> t option -> t option -> VarGen.loc -> (t * t * t)

val subst_type : (typ * typ) list -> t -> t
