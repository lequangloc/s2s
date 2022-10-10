
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


let string_of c= match c with
  | DataDecl d -> (Inode.string_of d)  ^ "."
  | PredDecl p -> (Ipred.string_of p)  ^ "."
  | RelDecl _ -> "RelDecl"
  | EntailCheck (f1, f2, _,_) -> "checkentail " ^ (Iformula.string_of f1) ^ " |- "
        ^ (Iformula.string_of f2) ^ "."
  | SatCheck (f, e) -> begin
      let exp =  match e with
          | None -> " "
          | Some v -> "[" ^( Out.string_of v) ^  "] "
      in
        "checksat" ^exp^ (Iformula.string_of f)  ^ "."
    end
  (* | Validate _ -> "Validate" *)
  | EmptyCmd -> "EmptyCmd"
