(*
data structure declaration
*)

open Globals
open Gen.Basic
open Gen
open VarGen
open Exc.GTable

type data_decl = {
    data_name : ident;
    data_fields : (typed_ident * loc) list;
    data_parent_name : ident;
    data_pos : loc;
    data_is_template: bool }

type t = data_decl

let rec string_of d=
  "\ndata " ^ d.data_name ^ " {\n" ^ (string_of_fields d.data_fields "\n") ^ "\n}."

and string_of_field (d, pos(* , il *)) = match d with
  | (t, i)             -> (* (if il then "inline " else "") ^ *)
        (string_of_typ t) ^ " " ^ i ^ ";"

and string_of_fields l c = match l with
  | []               -> ""
  | h::[]            -> "  " ^ string_of_field h
  | h::t             -> "  " ^ (string_of_field h)
        ^ ";" ^ c ^ (string_of_fields t c)

let mk dn dflds parent_id pos is_template=
  { data_name = dn;
    data_fields = dflds;
    data_parent_name = parent_id;
    data_pos = pos;
    data_is_template = is_template}

let gen_field_ann t=
  match t with
  | Named _ -> fresh_any_name field_rec_ann
  | _ -> fresh_any_name field_val_ann


let get_field_typed_id d =
  match d with
  | (tid,_) -> tid

(**
 * Extract the field name from a field declaration
 **)
let get_field_name f = snd (get_field_typed_id f)

(**
 * Extract the field name from a field declaration
 **)
let get_field_typ f = fst (get_field_typed_id f)

(**
 * Extract the field position from a field declaration
 **)
let get_field_pos f =
  match f with
  | (_,p) -> p

let rec look_up_data_def (defs : t list) (name : ident) =
  match defs with
    | d :: rest -> if d.data_name = name then d else
        look_up_data_def rest name
    | [] ->
          let msg = ("Cannot find definition of data structure " ^ name) in
          Gen.report_error no_pos msg


let rec look_up_all_fields (ddefs : t list) (c : t) =
  let current_fields = c.data_fields in
  (* expand the inline fields *)
  (* let current_fields = expand_inline_fields ddefs current_fields in *)
  if Ustr.str_eq c.data_name "Object" then
    []
  else
    let parent = (look_up_data_def ddefs c.data_parent_name) in
    current_fields @ (look_up_all_fields ddefs parent)

let look_up_all_fields_cname ddefs (c : ident) = 
  let ddef = look_up_data_def ddefs c in
  look_up_all_fields ddefs ddef

let rec look_up_types_containing_field (defs : t list) (field_name : ident) =
  match defs with
  | [] -> []
  | d::t -> let temp = look_up_types_containing_field t field_name in
    if (List.exists (fun x -> (get_field_name x) = field_name) d.data_fields) then
      d.data_name :: temp
    else temp

let get_type_of_field ddef field_name =
  let tids = List.map get_field_typed_id ddef.data_fields in
  try
    let field_typed_id = List.find (fun x -> (snd x = field_name)) tids in
    fst field_typed_id
  with
  | Not_found -> UNK


let rec get_type_of_field_seq ddefs root_type field_seq =
  match field_seq with
    | [] -> root_type
    | f::t -> (match root_type with
        | Named c -> (try
            let ddef = look_up_data_def ddefs c in
            let ft = get_type_of_field ddef f in
            (match ft with
              | UNK -> Error.report_error {
                    Error.error_loc = no_pos;
                    Error.error_text = "[get_type_of_field_seq] Compound type " ^ c ^ " has no field " ^ f ^ "!" }
              | _ -> get_type_of_field_seq ddefs ft t)
          with
            | Not_found -> Error.report_error {
                  Error.error_loc = no_pos;
                  Error.error_text = "[get_type_of_field_seq] Either data type " ^ c ^ " cannot be found!" })
        | _ -> Error.report_error {
              Error.error_loc = no_pos;
              Error.error_text = "[get_type_of_field_seq] " ^ (string_of_typ root_type) ^ " is not a compound type!" })


let is_data_type_identifier (ddefs : data_decl list) id =
  List.exists (fun x -> x.data_name = id) ddefs


let is_not_data_type_identifier (ddefs : data_decl list) id =
  not (is_data_type_identifier ddefs id)

let rec compute_typ_size ddefs t =
  let res = match t with
    | Named data_name -> (try
        let ddef = look_up_data_def ddefs data_name in
        List.fold_left (fun a f ->
            let fs = 1 in a + fs) 0 ddef.data_fields
      with | Not_found -> Error.report_error { Error.error_loc = no_pos; Error.error_text = "[compute_typ_size] input type does not exist."})
    | _ -> 1 in
  res

let rec compute_field_offset ddefs data_name accessed_field =
  try
    let ddef = look_up_data_def ddefs data_name in
    (* Accumulate the offset along the way *)
    let offset,found = List.fold_left (fun (a, found) f ->
        if (found) then (a, found) (* Once found, just keep constant*)
        else let fn = get_field_name f in
        (* let ft = get_field_typ f in *)
        if (fn = accessed_field) then (* Found the field *)
          a,true
        else a + 1, false)
      (0,false) ddef.data_fields in
    (* The field is not really a field of the data type ==> raise error. *)
    if (not found) then
      Error.report_error { Error.error_loc = no_pos;
      Error.error_text = "[compute_field_offset] " ^ "The data type " ^ data_name ^ " does not have field " ^ accessed_field }
    else
      offset
  with
    | Not_found -> Error.report_error { Error.error_loc = no_pos;
      Error.error_text = "[compute_field_offset] is call with non-existing data type." }


(**
 *  Compute the offset of the pointer indicated by a field sequence with
 *          respect to the root (that points to a type with name data_name)
 **)
and compute_field_seq_offset ddefs data_name field_sequence =
  let res,_ =
    List.fold_left (fun (a,dname)  field_name ->
        let offset = compute_field_offset ddefs dname field_name in
        (* Update the dname to the data type of the field_name *)
        try
          let ddef = look_up_data_def ddefs dname in
          let field_type = get_type_of_field ddef field_name in
          begin
            a + offset, string_of_typ field_type
          end
        with
          | Not_found -> Error.report_error { Error.error_loc = no_pos;
          Error.error_text = "[compute_field_seq_offset]: " ^ dname ^ " does not exists!" } )
        (0,data_name)  field_sequence in
  res

(*************************************************************)
(* Building the graph representing the class hierarchy       *)
(*************************************************************)

type ch_node = { ch_node_name : ident
(* mutable ch_node_class : data_decl option *) }

module CD = struct
  type t = ch_node
  let compare c1 c2 = compare c1.ch_node_name c2.ch_node_name
  let hash c = Hashtbl.hash c.ch_node_name
  let equal c1 c2 = (c1.ch_node_name = c2.ch_node_name)
end

module CH = Graph.Imperative.Digraph.Concrete(CD)
module TraverseCH = Graph.Traverse.Dfs(CH)

module W = struct
  type label = CH.E.label
  (* type edge = CH.E.edge *)
  type t = int
  let weight x = 1
  let zero = 0
  let add = (+)
  let compare = compare
end

module PathCH = Graph.Path.Dijkstra(CH)(W)

let class_hierarchy = CH.create ()

let build_hierarchy (ddecls : t list) =
  (* build the class hierarchy *)
  let add_edge (cdef : data_decl) = 
    CH.add_edge class_hierarchy (CH.V.create {ch_node_name = cdef.data_name})
        (CH.V.create {ch_node_name = cdef.data_parent_name}) in
  let add_edge cdef =
    let pr cdef = cdef.data_name^"<:"^cdef.data_parent_name in
    Debug.no_1 "add_edge" pr (fun _ -> "") add_edge cdef in
  let (todo_unknown:unit list) = List.map add_edge ddecls in
  if TraverseCH.has_cycle class_hierarchy then begin
    print_string ("Error: Class hierarchy has cycles\n");
    failwith ("Class hierarchy has cycles\n");
  end

(*
  see if c1 is sub class of c2 and what are the classes in between.
*)
let exists_path (c1 : ident) (c2 : ident) :bool =
  if c2="null" then true
  else
    try
      let todo_unknown = PathCH.shortest_path class_hierarchy
        (CH.V.create {ch_node_name = c1})
        (CH.V.create {ch_node_name = c2}) in
      true
    with
      | _ -> false

let exists_path c1 c2 =	Debug.no_2(* _loop *) "exists_path" pr_id pr_id  string_of_bool exists_path c1 c2

(* (\* is t1 a subtype of t2 *\) *)
let sub_type2 (t1 : typ) (t2 : typ) =
  if is_node_typ t1 && is_node_typ t2 then
    exists_path (string_of_typ t1) (string_of_typ t2)
  else false

let sub_type t1 t2 = Exc.GTable.sub_type t1 t2 || sub_type2 t1 t2

let compatible_types (t1 : typ) (t2 : typ) = sub_type t1 t2 || sub_type t2 t1

let inbuilt_build_exc_hierarchy () =
  (* let () = (exlist # add_edge "Object" "") in *)
  (* let () = (exlist # add_edge "String" "Object") in *)
  (* let () = (exlist # add_edge raisable_class "Object") in *)
  let _  = exlist # add_edge top_flow "" in
  (* let () = (exlist # add_edge c_flow top_flow) in *)
  (* let () = (exlist # add_edge "__abort" top_flow) in *)
  (* let () = (exlist # add_edge n_flow c_flow) in *)
  (* let () = (exlist # add_edge abnormal_flow c_flow) in *)
  (* let () = (exlist # add_edge raisable_class abnormal_flow) in *)
  (* let () = (exlist # add_edge "__others" abnormal_flow) in *)
  (* let () = (exlist # add_edge ret_flow "__others") in *)
  (* let () = (exlist # add_edge loop_ret_flow "__others") in *)
  (* let () = (exlist # add_edge cont_top "__others") in *)
  (* let () = (exlist # add_edge brk_top "__others") in *)
  (* let () = (exlist # add_edge spec_flow "__others") in *)
  (* let () = (exlist # add_edge mayerror_flow top_flow) in *)
  (* let () = (exlist # add_edge error_flow mayerror_flow) in *)
  (* let () = (exlist # add_edge n_flow mayerror_flow) in *)
  (* let () = (exlist # add_edge bfail_flow top_flow) in *)
  (* let () = (exlist # add_edge false_flow top_flow) in *)
  (* let () = (exlist # add_edge false_flow bfail_flow) in *)
  ()

let build_exc_hierarchy (clean:bool) (ddecls : t list) =
  (* build the class hierarchy *)
  let todo_unknown = List.map (fun c-> (exlist # add_edge c.data_name c.data_parent_name)) (ddecls) in
  let () = if clean then (exlist # remove_dupl ) in
  if (exlist # has_cycles) then begin
    print_string ("Error: Exception hierarchy has cycles\n");
    failwith ("Exception hierarchy has cycles\n");
  end

let build_exc_hierarchy (clean:bool) (ddecls : t list)  =
  let pr _ = exlist # string_of in
  Debug.no_1 "build_exc_hierarchy" pr pr (fun _ -> build_exc_hierarchy clean ddecls) clean
