open Globals
open Gen.Basic
open VarGen

type exp =
  | Ann_Exp of (exp * typ * loc)
  | Null of loc
  | Var of ((ident * primed) * loc)
(* variables could be of type pointer, int, bags, lists etc *)
  | IConst of (int * loc)
  | FConst of (float * loc)
  | SConst of (ident * loc )
  | CConst  of (int * loc)
  | Add of (exp * exp * loc)
  | Subtract of (exp * exp * loc)
  | Mult of (exp * exp * loc)
  | Div of (exp * exp * loc)
  | Max of (exp * exp * loc)
  | Min of (exp * exp * loc)
(* bag expressions *)
  | Bag of (exp list * loc)
  | BagUnion of (exp list * loc)
  | BagIntersect of (exp list * loc)
  | BagDiff of (exp * exp * loc)
  | TypeCast of (typ * exp * loc)
  | ArrayAt of ((ident * primed) * (exp list) * loc)
       (*String expressions*)
  (* | Sleng of (Var.t * loc) *)
  | Concat of (exp * exp * loc)


and t = exp

val string_of : t -> string

val typ_of_exp : t -> typ

val mkAnnExp: t -> typ -> loc -> t

val mkNull: loc -> t

val mkVar : (ident * primed) -> loc -> t

val mkIConst : int -> loc -> t

val mkFConst : float -> loc -> t

val mkSConst : ident -> loc -> t

val mkCConst : int -> loc -> t

val mkAdd : t -> t -> loc -> t

val mkSubtract : t -> t -> loc -> t

val mkMult : t -> t -> loc -> t

val mkDiv : t -> t -> loc -> t

val mkMax : t -> t -> loc -> t

val mkMin : t -> t -> loc -> t

val mkBag : t list -> loc -> t

val mkBagUnion : t list -> loc -> t

val mkBagIntersect : t list -> loc -> t

val mkBagDiff : t -> t -> loc -> t

val mkTypeCast : typ -> t -> loc -> t

val mkArrayAt : (ident * primed) -> t list -> loc -> t

val mkConcat: t -> t -> loc -> t

val combine_vars : t -> t -> (ident * primed) list

val fv : t -> (Globals.ident * VarGen.primed) list

val fresh_var : (ident*primed) -> (ident*primed)

val fresh_vars : (ident*primed) list -> (ident*primed) list

val eq_var : (ident*primed) -> (ident*primed) -> bool

val e_apply_one: (ident*primed) * (ident*primed) -> t -> t

val e_apply_one_list : (ident*primed) * (ident*primed) -> t list -> t list

val v_apply_one: (ident*primed) * (ident*primed) -> (ident *primed ) -> (ident*primed)
