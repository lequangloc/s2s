open Globals

open Cpure

val pure_tp: Others.tp_type ref

val start_prover : unit -> unit

val stop_prover : unit -> unit

val tp_is_sat_no_cache: bool -> Cpure.t -> string -> bool

val is_sat : ?cex:bool -> Cpure.t -> bool

val is_sat_chc : Cpred.t list -> Cformula.t -> Out.t

val imply : Cpure.t -> Cpure.t -> bool

val simplify : Cpure.t -> Cpure.t

val pairwisecheck: Cpure.t -> Cpure.t
