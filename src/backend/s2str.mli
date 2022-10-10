open Globals



val check_sat : Cpure.t list -> Cpure.t list -> Cpure.t list -> Cpure.t list
  -> int
  -> (Out.outcome * ((Var.t * Exp.t) list))
