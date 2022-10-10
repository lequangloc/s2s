open Globals
open VarGen
open Out

module IN = Inode
module IP = Ipred
module IF = Iformula

type icmd_sat = IF.t * (outcome option)

and icmd_ent = IF.t * IF.t * bool * (outcome option)

and command =
  | DataDecl of IN.data_decl
  | PredDecl of IP.pred_decl
  | RelDecl of Irel.rel_decl
  | EntailCheck of icmd_ent
  | SatCheck of icmd_sat
  | EmptyCmd


and t = command


val string_of : t -> string
