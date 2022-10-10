
open Camlp4
open Globals
open Gen.Basic
open ParserAhead
open ParderUtil
open Token
open Cmd
open Inode

module DD=Debug
module F = Iformula
module P = Ipure

module SHGram = Camlp4.Struct.Grammar.Static.Make(Lexer.Make(Token))

let sl_formula = SHGram.Entry.mk "sl_formula"

EXTEND SHGram

GLOBAL:  sl_formula;
  sl_formula:[[ t = formulas;  -> t ]];


(**************************************)
(* composite formula *)
(**************************************)


(**************************************)
(* symbolic heap*)
(**************************************)



END;;

