open Globals
open Gen
open VarGen

module type SUBTERM =
sig
  type t
  val string_of : t -> string
  val equal : t -> t -> bool
end;;

(* a function for subterm relationship in cyclic proofs *)

module FSubTerm =
    functor (Elt : SUBTERM) ->
struct
  type t = Elt.t list

  let string_of = pr_list Elt.string_of

  let mk xs = xs

  let append xs1 xs2 = xs1@xs2

  let mem (a:Elt.t) xs = List.exists (fun v1 -> Elt.equal a v1) xs

end;;

