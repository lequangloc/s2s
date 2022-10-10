open Globals
open Gen
open VarGen

module PeN = CpredNode

module SL_SUBTERM_ELT = struct
  type t = PeN.t
  let string_of = PeN.string_of

  let equal  = PeN.equal
end;;

module SUBT = Subterm.FSubTerm(SL_SUBTERM_ELT)
