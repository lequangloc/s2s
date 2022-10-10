open Globals
open Gen
open VarGen


module type EDGE_LBL =
sig
  type t
  val empty : t
  val is_empty : t -> bool
  val string_of : t -> string
  val subst : (Var.t * Var.t) list -> t -> t
end;;

module FEdge =
    functor (Lbl : EDGE_LBL) ->
struct
  type edge = {
      from_id: int;
      to_id: int;
      label: Lbl.t;
  }

  type t= edge

  let string_of_label = Lbl.string_of

  let string_of e=
    "(" ^
        (string_of_int e.from_id) ^"," ^
        (string_of_label e.label) ^"," ^
        (string_of_int e.to_id) ^
        ")"

  let mk frid tid l=
    { from_id = frid;
    to_id = tid ;
    label = l;}

  let next_x edges from_id=
    List.fold_left (fun r e ->
        if e.from_id == from_id then
          r@[(e.to_id, e)]
        else r
    ) [] edges

  let next edges from_id=
    let pr1 = pr_list string_of in
    let pr2 = pr_list (pr_pair string_of_int string_of) in
    Debug.no_2 "edge.next" pr1 string_of_int pr2
        (fun _ _ -> next_x edges from_id) edges from_id

  let search edges from_id to_id=
  List.find (fun e -> e.from_id == from_id && e.to_id == to_id) edges

  let subst sst e=
    let n_e = {e with
        label = Lbl.subst sst  e.label;} in
    n_e

end;;
