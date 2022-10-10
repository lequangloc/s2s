open VarGen
open Camlp4
open Globals
open Camlp4.PreCast
open Token


(* module SLGram: *)
(* sig *)
(*    (\* val sprog : Camlp4.Sig.Entry.t -> Cmd.t list *\) *)
(* end;; *)

(* val sprog : Sleekcommons.command list SLGram.Entry.t *)

val parse_sl: string -> char Stream.t -> Icmd.t list
