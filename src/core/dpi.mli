open Globals
open Ustr
open VarGen
open Gen.Basic

module CF = Cformula
module CP = Cpure
module DD = Debug


val is_dpi_self_rec : ident -> Var.t list -> CP.t -> bool -> bool * (CP.t list)

val to_pure_self_rec : ident -> Var.t list -> bool -> (String.t * (Var.t list * CP.t)) list -> CF.t -> bool * ((ident * Var.t list * CP.t) list)
