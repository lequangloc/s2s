open Globals
open Gen
open VarGen

open Com

module CF = Cformula

module EN = EntNode
module N = EntNode.ENTNODE
module E = EntEdge.ENTEDGE
module BL = StrEdge.STREDGE

let tree_id = ref (0 : int)

type cyc_tree = {
  m_tree_id : int;
  mutable m_node_ids : int list;
  mutable m_term : bool;
  mutable m_invalid_node_id : int option;
}

type t = cyc_tree

let string_of (t: t)=
  "tree id: " ^ (string_of_int t.m_tree_id) ^
      "\nnodes: " ^ ((pr_list string_of_int) t.m_node_ids) ^
      "\n[term: " ^ (string_of_bool t.m_term) ^ "; cex: " ^ ((pr_option string_of_int) t.m_invalid_node_id ) ^"]\n"

let get_next_id () =
  let r = !tree_id in
  let () = tree_id := !tree_id + 1 in
  r

let get_cur_id () = !tree_id

let reset_cur_id () =
  let () = tree_id := 0 in
  ()

let make id node_ids is_term invalid_node_id=
  {
      m_tree_id = id;
      m_node_ids = node_ids;
      m_term = is_term;
      m_invalid_node_id = invalid_node_id;
  }

let dump_tree  = make (-1) [] true None

let update_tree_invalid t node_id=
  let new_t = {t with m_invalid_node_id = Some node_id} in
  new_t
