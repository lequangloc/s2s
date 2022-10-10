open Globals



val check_sat : Cformula.t   -> int  -> (Out.outcome * (Cformula.t option))
