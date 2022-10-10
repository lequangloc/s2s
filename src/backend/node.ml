open Globals
open Gen
open VarGen


open Com

module type NODE_DATA =
sig
  type t
  val string_of : t -> string
  val string_of_short : t -> string
  val eval : Cpred.t list -> bool -> (Cpure.t * Cpure.t) list-> t -> Out.outcome * (Cpure.t * Cpure.t) list
  val eval_all : bool -> t -> Out.outcome
end;;

module FNode =
    functor (Elt : NODE_DATA) ->
struct
  type node = {
     id: int;
     data: Elt.t;
     parent: int;
     mutable child: int list;
     height: int;
     mutable status: nstatus;
     (* 0 : open (default); 1: unsat; 2: back-linked; 3: sat; 4: sat with condition for composition; 5: reduced *)
  }

  type t = node

  let string_of n=
   "id: " ^ string_of_int n.id ^ "\n" ^
       "data: " ^ (Elt.string_of_short n.data) ^ "\n" ^
       "parent: " ^ (string_of_int n.parent) ^ "\n" ^
       "children: " ^ (pr_list string_of_int) n.child ^ "\n" ^
       "h:" ^ (string_of_int n.height) ^ "\n" ^
       "status = " ^ (string_of_node_status n.status) ^ "\n"

 let mk i e pid child_ids h s=
   { id = i;
   data = e;
   parent = pid;
   child = child_ids;
   height = h;
   status = s;
   }

 let update_status n res=
   let () = if res == Out.UNSAT then
     let () = n.status <- Nunsat in
     ()
   else if res == Out.SAT then
     n.status <- Nsat
   else if res == Out.SATCM then
     n.status <- NsatCC
   else ()
   in
   ()

 let update_ent_status n res=
   let () = if res == Out.VALID then
     let () = n.status <- Nvalid in
     ()
   else if res == Out.INVALID then
     n.status <- Ninvalid
   else ()
   in
   ()

 let eval pdecls heap_only n =
   let res, _ = Elt.eval pdecls heap_only [] n.data in
   let () = update_status n res in
   res

 let eval_ent pdecls heap_only ass n =
   let res, ass =  Elt.eval pdecls heap_only ass n.data in
   let () = update_ent_status n res in
   res, ass


 let eval_all bho n =
   let res = Elt.eval_all bho n.data in
   let () = update_status n res in
   res

end;;


