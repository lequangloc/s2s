open Globals
open Gen.Basic
open VarGen

module IP = Ipure
module IH = Iheap
module ISH = Isymheap
module IF = Iformula


let gen_name_pairs_heap pred_decls pname h0=
  let rec helper h=
    match h with
      | IH.Star (h1, h2, _) -> (helper h1)@(helper h2)
      | IH.PtoNode _
      | IH.HeapNode2 _ -> []
      | IH.PredNode { IheapNode.hpred_name = c } -> (try
         let todo_unk = Iprog.lookup_pred_defn pred_decls c in
         [(pname, c)]
        with | Not_found ->
            if Cgraph.pred_scc_obj # in_dom c then [(pname,c)]
            else []
      )
      | IH.HEmp
      | IH.HTrue
      | IH.HFalse -> []
  in
  helper h0

let gen_name_pairs_formula pred_decls (name: ident) f0=
  gen_name_pairs_heap pred_decls name f0.ISH.base_heap


let gen_name_pairs_cof_x pred_decls name f0=
  let rec helper f=
    match f with
      | IF.Base f -> gen_name_pairs_formula pred_decls name f
      | IF.Exists (f, _) -> gen_name_pairs_formula pred_decls name f
      | IF.Or (f1, f2, _) -> (helper f1)@(helper f2)
  in
  helper f0

let gen_name_pairs_cof pred_decls name f0=
  let pr1 = pr_list Ipred.string_of in
  let pr2 = IF.string_of in
  let pr3 = pr_list (pr_pair pr_id pr_id) in
  Debug.no_3 "gen_name_pairs_cof" pr1 pr_id pr2 pr3
      (fun _ _ _ -> gen_name_pairs_cof_x pred_decls name f0)
      pred_decls name f0
