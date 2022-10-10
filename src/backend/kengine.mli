open Globals

open Cpure
open Dpure


val check_sat_str : Cpure.t list -> (Out.outcome * Cformula.t option)

val str_normalize : Cpure.t -> (Cpure.t list * Cpure.t list * Cpure.t list * Cpure.t list)

val check_sat : Cpred.t list -> Cformula.t  -> (Out.outcome * Cformula.t option)
