open Globals
open VarGen
open Gen.Basic

class prog_decl src_files =  object(self)
  val m_src_files = src_files
  val m_include_decls : ident list = []
  val mutable m_data_decls : Cnode.data_decl list = []
  (* val global_var_decls : exp_var_decl list; *)
  (* val logical_var_decls : exp_var_decl list; *)
  (* val enum_decls : enum_decl list; *)
  val mutable m_pred_decls : Cpred.pred_decl list = []
  val mutable m_rel_decls : Crel.rel_decl list = []
  (* mutable hp_decls : hp_decl list; *)
  (* mutable rel_ids : (typ * ident) list; *)
  (* mutable hp_ids : (typ * ident) list; *)
  (* proc_decls : proc_decl list; *)
  (* mutable lemma_decls : lemma_decl_list list; *)
  val mutable m_vc_sats : Ccmd.cmd_sat list = []
  val mutable m_vc_ents  = []


 method string_of ()  = (string_marker "core program") ^
   (String.concat "\n\n" (List.map Cnode.string_of m_data_decls)) ^ "\n\n" ^
  (String.concat "\n\n" (List.map Cpred.string_of m_pred_decls)) ^ "\n\n" ^
  (String.concat "\n\n" (List.map Crel.string_of m_rel_decls)) ^ "\n\n" ^
  (String.concat "\n\n" (List.map Ccmd.string_of_cmd_sat m_vc_sats)) ^ "\n\n" ^
  (String.concat "\n\n" (List.map Ccmd.string_of_cmd_ent  m_vc_ents))
^ (string_marker "end core")

 method set_data_decls decls =
   let () =  m_data_decls <- decls in
   ()

 method set_pred_decls decls =
   let () =  m_pred_decls <- decls in
   ()

 method get_pred_decls () = m_pred_decls

 method set_sat_queries queries =
   let () =  m_vc_sats <- queries in
   ()

  method set_ent_queries queries =
   let () =  m_vc_ents <- queries in
   ()

 method get_sat_queries () = m_vc_sats

 method get_ent_queries () = m_vc_ents

 method add_data_decls decls =
   let () =  m_data_decls <- m_data_decls@decls in
   ()

 method add_pred_decls decls =
   let () =  m_pred_decls <- m_pred_decls@decls in
   ()


end;;
