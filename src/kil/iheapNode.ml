open Globals
open Gen.Basic
open VarGen

type pto = {
    heap_node : (ident * primed);
    heap_name : ident;
    heap_deref : int;
    heap_derv : bool;
    heap_arguments : Iexp.t list;
    heap_pos : loc }

(*with field name annotation*)
and heap2 = {
    heap2_node : (ident * primed);
    heap2_name : ident;
    heap2_deref : int;
    heap2_derv : bool;
    heap2_arguments : (ident * Iexp.t) list;
    heap2_pos : loc }

and hpred = {
    (* heap2_node : (ident * primed); *)
    hpred_name : ident;
    hpred_deref : int;
    hpred_derv : bool;
    hpred_arguments : Iexp.t list;
    hpred_pos : loc }

let string_of_pto h =
  ((string_of_pid h.heap_node) ^ "::" ^ h.heap_name ^
       ((pr_list_angle Iexp.string_of) h.heap_arguments) )

let string_of_heap2 h= ((string_of_pid h.heap2_node) ^ "::" ^ h.heap2_name ^
       ((pr_list_angle (pr_pair pr_id Iexp.string_of)) h.heap2_arguments) )

let string_of_hpred h= (h.hpred_name ^
       ((pr_list_round  Iexp.string_of) h.hpred_arguments) )

let mkPtoNode c id deref dr hl l={
    heap_node = c;
    heap_name = id;
    heap_deref = deref;
    heap_derv = dr;
    heap_arguments = hl;
    heap_pos = l }

let mkNode2 c id deref dr hl l={
    heap2_node = c;
    heap2_name = id;
    heap2_deref = deref;
    heap2_derv = dr;
    heap2_arguments = hl;
    heap2_pos = l }


let mkPredNode id deref dr hl l={
    hpred_name = id;
    hpred_deref = deref;
    hpred_derv = dr;
    hpred_arguments = hl;
    hpred_pos = l }



let node2_to_pto_x ddecls (h0 : heap2) : pto =
(* match named arguments with
     formal parameters to generate a list of    *)
  (* position-based arguments.
     If a parameter does not appear in args,     *)
  (* then it is instantiated to a fresh name.    *)
  let rec match_args (params : ident list) field_ann_args res: Iexp.t list =
    match params with
    | p :: rest ->
          let tmp2 = List.filter (fun a -> (fst a) = p) field_ann_args in
          let tmp3 =
            (match tmp2 with
              | [(_, Iexp.Var ((e1, e2), e3)) ] -> Iexp.Var ((e1, e2), e3)
              | [(_, Iexp.Null p)] -> (Iexp.Null p)
              | [(_, Iexp.IConst (i, p))] -> Iexp.IConst (i, p)
              | [(_, Iexp.FConst (i, p))] -> Iexp.FConst (i, p)
              | _ -> let fn = (qvar_id ^ (fresh_trailer())) in
                Iexp.Var ((fn, Unprimed), h0.heap2_pos) )
          in
          match_args rest field_ann_args (res@[tmp3])
    | [] -> res
  in
  (* try *)
  (*   let vdef = List.find (fun pdef -> *)
  (*       Ustr.str_eq pdef.Ipred.pred_name h0.heap2_name) pdecls in *)
  (*   let hargs = match_args pdef.Ipred.pred_vars h0.heap2_arguments [] in *)
  (*   let h = { hpred_name = h0.heap2_name; *)
  (*             hpred_deref = h0.heap2_deref; *)
  (*             hpred_derv = h0.heap2_derv; *)
  (*             hpred_arguments = (fst h0.heap2_node)::hargs; *)
  (*             hpred_pos = h0.heap2_pos; *)
  (*   } *)
  (*     h *)
  (* with *)
  (*   | Not_found -> *)
          let ddef = List.find (fun ddef ->
              Ustr.str_eq ddef.Inode.data_name h0.heap2_name) ddecls
          in
          let params = List.map (fun ((_, fn),_) -> fn) ddef.Inode.data_fields in
          let hargs= match_args params h0.heap2_arguments [] in
          let h = { heap_node = h0.heap2_node;
          heap_name = h0.heap2_name;
          heap_deref = h0.heap2_deref;
          heap_derv = h0.heap2_derv;
          heap_arguments = hargs;
          heap_pos = h0.heap2_pos;
          } in
          h

let node2_to_pto ddecls (h0 : heap2) : pto =
  Debug.no_1 "node2_to_pto"
    (fun f -> string_of_heap2 f)
    (fun f -> string_of_pto f)
      (fun _ -> node2_to_pto_x ddecls h0) h0
