(*
This module is for the data
 m_iprog
 m_cpog

*)

open Globals
open Ustr
open VarGen
open Gen.Basic


class kdata src_files parse=  object(self)
  val m_iprog = new Iprog.prog_decl src_files parse
  val m_cprog = new Cprog.prog_decl src_files

  method get_irel_decls () = m_iprog # get_rel_decls ()
  method get_idata_decls () = m_iprog # get_data_decls ()
  method get_ipred_decls () = m_iprog # get_pred_decls ()
  method get_isat_queries () = m_iprog # get_sat_queries ()
  method get_ient_queries () = m_iprog # get_ent_queries ()

  method set_cdata_decls ddecls =
    m_cprog # set_data_decls ddecls

  method set_cpred_decls pdecls =
    m_cprog # set_pred_decls pdecls

  method get_cpred_decls () =
    m_cprog # get_pred_decls ()

  method set_csat_queries queries =
    m_cprog # set_sat_queries queries

  method set_cent_queries queries =
    m_cprog # set_ent_queries queries

  method get_csat_queries () =
    m_cprog # get_sat_queries ()

  method get_cent_queries () =
    m_cprog # get_ent_queries ()

  method do_parse_iprog () =
    let () = m_iprog # do_parse () in
    let () = if !VarGen.ent_false_to_sat then
      m_iprog # do_trans_ent_false_to_sat ()
    else () in
    ()

  method check_exist_type (t : typ) pos: typ =
    match t with
      | Named id -> (try
          let ddef = m_iprog#lookup_data_defn id
          in Named id
        with
          | Not_found -> (try
              let pdef = m_iprog#lookup_pred_defn id
              in Named id
            with
              |  Not_found -> Error.report_error
                     {
                         Error.error_loc = pos;
                         Error.error_text = id ^ " is neither data, nor pred";
                     }
            ))
      | p -> p

  method print_k ()=
    let () = if !VarGen.print_k then
      print_endline_quiet (m_iprog # string_of ())
    else () in
    ()

  method print_core ()=
    let () = if !VarGen.print_core then
      print_endline_quiet (m_cprog # string_of ())
    else () in
    ()

end;;
