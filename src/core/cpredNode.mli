open Globals
open Gen.Basic
open VarGen


type hpred = {
    hpred_name : ident;
    hpred_derv : bool;
    hpred_arguments : Var.t list;

    (* for sat/ent cyclic proofs *)
    hpred_unfold_num : int;
    hpred_unfold_seq : int;
    mutable hpred_unfold_step : int;
    (* 0: non-progressing view each unfolding
       1: progressing view each unfolding
    *)

    (*rhs quantifier instantiated*)
    hpred_rhs_inst: bool;

    hpred_pos : loc }

and t = hpred

val string_of : t -> string

val string_of_short : t -> string

val mk: ?un:int -> ?us:int -> ?ut:int -> ?inst:bool -> Globals.ident -> bool -> Var.t list  -> loc ->  t

val subst: (Var.t * Var.t) list -> t -> t

val bfs_cmp : t -> t -> int

val subst_type : (typ * typ) list -> t -> t

val equal : t -> t -> bool
