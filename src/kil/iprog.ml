open Globals
open VarGen
open Gen.Basic
open Exc.GTable
open Ustr

let lookup_pred_defn pred_decls name=
   let rec helper defns=
     match defns with
       | d::rest -> if str_eq d.Ipred.pred_name name then d else
           helper rest
       | [] -> let msg = ("Cannot find definition of predicate declaration " ^ name) in
         Gen.report_error no_pos msg
   in helper pred_decls

let lookup_data_defn ddecls name=
  let rec helper defns=
    match defns with
      | d::rest ->
            if str_eq d.Inode.data_name name then d else
              helper rest
      | [] -> let msg = ("Cannot find definition of data declaration " ^ name) in
        Gen.report_error no_pos msg
  in helper ddecls


class prog_decl src_files parse =  object(self)
  val m_src_files = src_files
  val m_parser = parse
  val m_include_decls : ident list = []
  val mutable m_data_decls : Inode.data_decl list = []
  (* val global_var_decls : exp_var_decl list; *)
  (* val logical_var_decls : exp_var_decl list; *)
  (* val enum_decls : enum_decl list; *)
  val mutable m_pred_decls : Ipred.pred_decl list = []
  val mutable m_rel_decls : Irel.rel_decl list = []
  (* mutable hp_decls : hp_decl list; *)
  (* mutable rel_ids : (typ * ident) list; *)
  (* mutable hp_ids : (typ * ident) list; *)
  (* proc_decls : proc_decl list; *)
  (* mutable lemma_decls : lemma_decl_list list; *)
  val mutable m_vc_sats :Icmd.icmd_sat list = []
  val mutable m_vc_ents :Icmd.icmd_ent list  = []


 method string_of ()  = (string_marker "input program") ^
   (String.concat "\n\n" (List.map Inode.string_of m_data_decls)) ^ "\n\n" ^
  (String.concat "\n\n" (List.map Ipred.string_of m_pred_decls)) ^ "\n\n" ^
  (String.concat "\n\n" (List.map Irel.string_of m_rel_decls)) ^ "\n\n" ^
  (String.concat "\n\n" (List.map (fun (f,e) ->  Icmd.string_of (Icmd.SatCheck (f,e))) m_vc_sats)) ^ "\n\n" ^
  (String.concat "\n\n" (List.map (fun (f1, f2, _,_) -> "checkentail " ^ (Iformula.string_of f1) ^ " |- "
        ^ (Iformula.string_of f2) ^ ".") m_vc_ents))
^ (string_marker "end input")

 method get_data_decls () = m_data_decls

 method get_pred_decls () = m_pred_decls

 method get_rel_decls () = m_rel_decls

 method get_sat_queries () = m_vc_sats

 method get_ent_queries () = m_vc_ents


 method lookup_pred_defn name= lookup_pred_defn m_pred_decls name
 method lookup_data_defn name= lookup_data_defn m_data_decls name

 method check_dupl_decl name=
   try
     let unk = List.find (fun dd -> string_eq dd.Inode.data_name name) m_data_decls in
     false
   with | Not_found -> begin
      try
        let unk =  List.find (fun pd -> string_eq pd.Ipred.pred_name name) m_pred_decls in false
      with | Not_found -> begin
          try
            let unk = List.find (fun reld -> string_eq reld.Irel.rel_name name) m_rel_decls in false
          with | Not_found -> begin
            true
          end
      end
   end

 method do_trans_ent_false_to_sat ()=
   let sat,ent = List.fold_left (fun (r1, r2) ((lhs, rhs, b, opt_ex) as e) ->
       if Iformula.isFalse rhs then
         begin
           let () = print_endline_quiet "do_trans_ent_false_to_sat" in
           let n_ex = match opt_ex with
             | Some ex -> begin match ex with
                 | Out.VALID -> Some Out.UNSAT
                 | Out.INVALID -> Some Out.SAT
                 | _ -> opt_ex
               end
             | None -> None
           in
           (r1@[(lhs, n_ex)], r2)
         end
       else (r1, r2@[e])
   ) ([], []) m_vc_ents in
   let () = m_vc_ents <- ent in
   let () = m_vc_sats <- m_vc_sats@sat in
   ()

 method process_data_decl ddecl=
   if self#check_dupl_decl ddecl.Inode.data_name then
     let () = m_data_decls <- m_data_decls @[ddecl] in
     (* let _ = Icfg.build_exc_hierarchy true iprog in *)
     (* let _ = exlist # compute_hierarchy  in *)
     (* let _ = iprog.I.prog_data_decls <- iprog.I.prog_data_decls@[iexc_def] in *)
     ()
   else begin
    report_error ddecl.Inode.data_pos (ddecl.Inode.data_name ^ " is already defined.")
   end

 method process_pred_decl pdecl=
   if self#check_dupl_decl pdecl.Ipred.pred_name then
     m_pred_decls <- m_pred_decls@[pdecl]
  else
    report_error pdecl.Ipred.pred_pos (pdecl.Ipred.pred_name ^ " is already defined.")


 method process_vc_ent e=
   let () =  m_vc_ents <-  m_vc_ents@[e] in
   ()

 method process_vc_sat (f, e)=
   let () =  m_vc_sats <-  m_vc_sats@[(f,e)] in
   ()

 method process_one_cmd c= match c with
  | Icmd.DataDecl d -> self # process_data_decl d
  | Icmd.PredDecl p -> self # process_pred_decl p
  | Icmd.RelDecl _ -> ()
  | Icmd.EntailCheck ent -> self # process_vc_ent ent
  | Icmd.SatCheck (f, e) -> self # process_vc_sat (f, e)
  (* | Icmd.Validate _ -> () *)
  | Icmd.EmptyCmd -> ()

 method do_parse () =
   let cmds = m_parser (List.hd m_src_files) in
   (* processing *)
   let iobj_def =  Inode.mk "Object" [] "" no_pos false in
   let iexc_def =  Inode.mk raisable_class [] "Object" no_pos false in
   let () = m_data_decls <- m_data_decls @ [iobj_def;iexc_def] in
  (* data and inductive pred*)
   let vcs = List.fold_left (fun acc c ->
       match c with
         | Icmd.DataDecl _ | Icmd.PredDecl _ | Icmd.RelDecl _ ->
               let () = self # process_one_cmd c in
               acc
         | Icmd.EmptyCmd -> acc
         | _ -> acc@[c]
   ) [] cmds in
  (* lemmas *)

  (* vc: sat/ent/validate. to pair validate and sat/ent *)
  List.iter self # process_one_cmd vcs


end;;

