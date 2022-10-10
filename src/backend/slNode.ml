open Globals
open Gen
open VarGen

open Com

module CF = Cformula
module CSH = Csymheap
module CH = Cheap
module CPeN = CpredNode
module CPoN = CptoNode
module CP = Cpure
module EQ = Eql

module SLU = SlUtil

module SL_NODE_DATA = struct
  type t_heap = {
      hpreds : CPeN.t list;
      hptos : CPoN.t list;
      qf_eql_f: EQ.t; (* quantifier-free equalities for back-link checking *)
      eql_f : EQ.t; (* normal form: if x|- * y|- in hptos then x!=null /\ y!=null /\ x!=y in eql_f *)
      ho_inv_preds: EQ.t; (* heap_only inv *)
  }

 type t_arith = {
     arith_pure : CP.t;
     inv_preds: CP.t;
  }

  type t = {
      elimed_eqs: (Var.t * Var.t) list;
      qvars : Var.t list;
      heap: t_heap;
      arith: t_arith;
  }

  let get_hvars e=
    List.map (fun dn -> dn.CPoN.hpto_node) e.heap.hptos

  let string_of_heap (e: t_heap)=
    "hpred = " ^ (String.concat "*" (List.map (CPeN.string_of) e.hpreds)) ^ "\n" ^
        "hptos = " ^ (String.concat "*" (List.map (CPoN.string_of) e.hptos)) ^ "\n" ^
        "qf_eql_f = " ^ ((EQ.string_of) e.qf_eql_f) ^ "\n" ^
        "eql_f = " ^ ((EQ.string_of) e.eql_f) ^ "\n"

  let string_of_arith (e: t_arith)=
    "arith_pure = " ^ ((CP.string_of) e.arith_pure) ^ "\n" ^
        "inv_preds = " ^ ((Cpure.string_of) e.inv_preds)  ^ "\n"


  let string_of (e: t)=
    "hvars:" ^ ((Var.string_of_list) (get_hvars e)) ^ " " ^
    "elimed_eqs:" ^ (pr_list (Var.string_of_pair) e.elimed_eqs) ^
        "\n" ^
    "Ex " ^ ((Var.string_of_list) e.qvars) ^ " ." ^
        "heap == " ^ (string_of_heap e.heap)  ^ "\n" ^
        "arith == " ^ (string_of_arith e.arith) ^ "\n"

  let string_of_heap_short (e: t_heap)=
    "hpred = " ^ (String.concat "*" (List.map (CPeN.string_of) e.hpreds)) ^ "\n" ^
        "hptos = " ^ (String.concat "*" (List.map (CPoN.string_of) e.hptos)) ^ "\n" ^
        "qf_eql_f = " ^ ((EQ.string_of) e.qf_eql_f) ^ "\n" ^
        "eql_f = " ^ ((EQ.string_of) e.eql_f) ^ "\n"

  let string_of_arith_short (e: t_arith)=
    "arith_pure = " ^ ((CP.string_of) e.arith_pure) ^ "\n" ^
        "inv_preds = " ^ ((Cpure.string_of) e.inv_preds)  ^ "\n"


  let string_of_short (e: t)=
     "hvars:" ^ ((Var.string_of_list) (get_hvars e)) ^ "\n" ^
     "elimed_eqs:" ^ (pr_list (Var.string_of_pair) e.elimed_eqs) ^ "\\n" ^
    "Ex " ^ ((Var.string_of_list) e.qvars) ^ ". " ^
        "heap == " ^ (string_of_heap_short e.heap)  ^ "\n" ^
        "arith == " ^ (string_of_arith_short e.arith) ^ "\n"

  let to_pure e=
    let equality = EQ.to_pure e.heap.eql_f in
    let p = if Cpure.isTrue e.arith.arith_pure then
       equality
    else
      CP.mkAnd (CP.mkAnd (equality) e.arith.arith_pure no_pos)  e.arith.inv_preds no_pos in
    p

  let is_unsat e=
    EQ.check_sat e.heap.eql_f == Out.UNSAT

  let is_heap_only e=
    CP.isTrue e.arith.arith_pure

  let elim_ex_null_var e=
    let null_svs, sst, n_eql_f = EQ.elim_ex_null_var e.heap.eql_f in
    if sst == [] then [], e
    else
      let n_hpreds = List.map (CPeN.subst sst) e.heap.hpreds in
      let n_hptos = List.map (CPoN.subst sst) e.heap.hptos in
      let n_h = {e.heap with hpreds = n_hpreds;
          hptos = n_hptos;
          eql_f = n_eql_f }
      in
      sst, {e with qvars = Var.diff e.qvars null_svs;
          heap = n_h;
      }

  let add_spec_null_var e=
    let eql = e.heap.eql_f in
    let n_eql = {eql with EQ.null_vars = eql.EQ.null_vars@[Var.null_var]} in
    let qf_eql = e.heap.qf_eql_f in
    let n_qf_eql = {qf_eql with EQ.null_vars = qf_eql.EQ.null_vars@[Var.null_var]} in
    let n_h = {e.heap with eql_f = n_eql;
        qf_eql_f = n_qf_eql;
    } in
    {e with heap = n_h}

  let split_quantifiers e=
    let eql = {e.heap.eql_f with EQ.qvars = []} in
    let n_h = {e.heap with eql_f = eql;} in
    e.qvars, {e with qvars = []; heap = n_h;}

  let add_quantifiers n_qvars e=
    let eql = {e.heap.eql_f with EQ.qvars = e.heap.eql_f.EQ.qvars@n_qvars} in
    let n_h = {e.heap with eql_f = eql;} in
    {e with qvars = e.qvars@n_qvars; heap = n_h;}

  let is_empty_heap_or_htrue e=
    e.heap.hptos == [] &&  e.heap.hpreds == []

  let h_fv e=
    let vn_vs = List.fold_left(fun r vn -> r@vn.CPeN.hpred_arguments) [] e.heap.hpreds in
    let vpn_vs = List.fold_left(fun r dn -> r@[dn.CPoN.hpto_node]@dn.CPoN.hpto_arguments) vn_vs e.heap.hptos in
    Var.remove_dups (vpn_vs@(EQ.fv e.heap.eql_f))

  let p_fv e=
    CP.fv e.arith.arith_pure

  let fv e=
    Var.diff ((h_fv e)@(p_fv e)) e.qvars

  let h_subst sst h_e=
    let vns = List.map (fun vn -> CPeN.subst sst vn) h_e.hpreds in
    let dns = List.map (fun dn -> CPoN.subst sst dn) h_e.hptos in
    { hpreds = vns; hptos = dns;
    qf_eql_f = EQ.subst sst h_e.qf_eql_f;
    eql_f =  EQ.subst sst h_e.eql_f;
    ho_inv_preds = EQ.subst sst h_e.ho_inv_preds;
    }

  let p_subst (sst: (Var.t * Var.t) list) a=
    { arith_pure = CP.subst_var sst a.arith_pure;
    inv_preds = CP.subst_var sst a.inv_preds}

  let subst_x (sst: (Var.t * Var.t) list) e=
    let qsvnames = (List.map Var.name_of e.qvars) in
    let sst = List.filter (fun (fr,_) -> not (List.mem (Var.name_of fr) qsvnames)) sst in
    if sst = [] then e else
    let n_h = h_subst sst e.heap in
    let n_a = p_subst sst e.arith in
    {e with heap = n_h; arith = n_a;}

  let subst sst e=
    let pr1 = pr_list Var.string_of_pair in
    Debug.no_2 "SLND.subst" pr1 string_of string_of
        (fun _ _ -> subst_x sst e) sst e

  let subst_qvars (sst: (Var.t * Var.t) list) e=
    if sst = [] then e else
    let n_qvars = List.filter (fun sv ->
        List.for_all (fun (sv1, _) -> not(Var.equal sv sv1)) sst) e.qvars in
    let n_h = h_subst sst e.heap in
    let n_a = p_subst sst e.arith in
    {e with qvars = n_qvars; heap = n_h; arith = n_a;}

  (*remove the first matched cpred*)
  let subtract_pred e vn=
    let n_h = {e.heap with hpreds = BList.remove_fst_eq
            CPeN.equal vn e.heap.hpreds} in
    {e with heap = n_h}

  let mkStarAnd_pred_arith e qavars vns a=
    let n_h = {e.heap with
        hpreds = vns@e.heap.hpreds} in
    let n_a = {e.arith with arith_pure = (*Cpure.add_quantifiers qavars*)(Cpure.mkAnd a e.arith.arith_pure no_pos);} in
    {e with qvars = e.qvars@qavars;
        heap = n_h;
        arith = n_a;
    }

  let reset_rinst e vns=
    let e1 = List.fold_left (fun r vn ->
        subtract_pred r vn
    ) e vns in
    let reset_vns = List.map (fun vn -> {vn with CPeN.hpred_rhs_inst =false}) vns in
    mkStarAnd_pred_arith e1 [] reset_vns (CP.mkTrue no_pos)

  (*remove the first matched pto*)
  let subtract_pto e dn=
    let n_h = {e.heap with hptos =  BList.remove_fst_eq
            CPoN.equal dn e.heap.hptos} in
    {e with heap = n_h}

  (* elim spatial unused qvars *)
  let elim_spatial_unused_qvars e=
    let h = e.heap in
    if h.hpreds == [] && h.hptos == [] then
      let sqvars, aqvars = List.partition (Var.is_node) e.qvars in
      (* let q_eqs = List.fold_left (fun r (v1, v2) -> *)
      (*     if (Var.mem v1 sqvars) then *)
      (*       r@[(v1, v2)] *)
      (*     else if (Var.mem v2 sqvars) then *)
      (*       r@[(v2, v1)] *)
      (*     else r *)
      (* ) [] h.eql_f.EQ.eqs in *)
      let n_qvars, n_eql_f = EQ.elim_ex_qvars sqvars ((* EQ.subst q_eqs *)  h.eql_f) in
      let n_h1 = {h with eql_f = n_eql_f} in
      {e with qvars = n_qvars@aqvars; heap = n_h1;}
    else
      e

  let fresh_quantifiers e=
    let n_qvars = Var.fresh_vars e.qvars in
    let sst = List.combine e.qvars n_qvars in
    let e1 = subst sst {e with qvars = []} in
    let n_h = {e1.heap with eql_f =
            {e1.heap.eql_f with qvars = n_qvars;};
        ho_inv_preds = {e1.heap.ho_inv_preds with  qvars = n_qvars;};
    } in
    {e1 with qvars = n_qvars; heap = n_h}

  let remove_dups e=
    let n_h = {e.heap with qf_eql_f = EQ.remove_dups e.heap.qf_eql_f;
        eql_f = EQ.remove_dups e.heap.eql_f;
    } in
    {e with heap = n_h}

  let increase_view_unfold_number e=
    let n_h = {e.heap with hpreds = List.map (fun n ->
        {n with CPeN.hpred_unfold_num = n.CPeN.hpred_unfold_num + 1}) e.heap.hpreds} in
    {e with heap = n_h}

  let combine_hvars hvars1 hvars2 =
    let comb_diseqs = List.fold_left (fun r sv ->
        r@(List.map (fun sv1 -> (sv1, sv)) hvars1)
    ) [] hvars2 in
    comb_diseqs


  let update_diseqs e new_diseqs=
    let eql = e.heap.eql_f in
    let eql1 = EQ.mkAnd_diseqs eql new_diseqs in
    let qf_eql1 = if not eql1.EQ.is_poss_sat then
      {e.heap.qf_eql_f with EQ.is_poss_sat = false}
    else EQ.mkAnd_diseqs e.heap.qf_eql_f new_diseqs in
    let n_h = {e.heap with eql_f = eql1;
        qf_eql_f = qf_eql1;
    } in
    {e with heap = n_h;}

  let update_star_new_nodes e svs=
    let rec helper svs res= match svs with
      | sv::rest ->
            let neqs = List.map (fun sv1 -> (sv, sv1)) rest in
            helper rest (res@neqs)
      | [] -> res
    in
    if svs == [] then e else
    (* update new diseqs and disnull_vars *)
    let cur_hvars = get_hvars e in
    let n_diseqs1 = combine_hvars cur_hvars svs in
    let n_diseqs2 = helper svs [] in
    (* let () = Debug.info_hprint (add_str  "e" *)
    (*     string_of_short) e no_pos in *)
    (* let () = Debug.info_hprint (add_str  "n_diseqs1" *)
    (*     (pr_list Var.string_of_pair)) n_diseqs1 no_pos in *)
    (* let () = Debug.info_hprint (add_str  "n_diseqs2" *)
    (*     (pr_list Var.string_of_pair)) n_diseqs2 no_pos in *)
    (* update *)
    let eql = e.heap.eql_f in
    let eql1 = EQ.mkAnd_diseqs eql (n_diseqs1@n_diseqs2) in
    let eql2 = EQ.mkAnd_disnull eql1 svs in
    (* let () = Debug.info_hprint (add_str  "eql2" *)
    (*     EQ.string_of) eql2 no_pos in *)
    let qf_eql2 = if not eql2.EQ.is_poss_sat then
      {e.heap.qf_eql_f with EQ.is_poss_sat = false}
    else e.heap.qf_eql_f in
    let n_h = {e.heap with eql_f = eql2;
        qf_eql_f = qf_eql2;
    } in
    {e with heap = n_h;}

  let eval _ bheap_only _  e=
    (* let rec pair_wire_diff ls_vs qvars= *)
    (*   match ls_vs with *)
    (*     | vs::rest -> if Var.diff vs qvars == [] && *)
    (*         (List.for_all (fun vs1 -> Var.intersect vs vs1 != []) rest) *)
    (*       then pair_wire_diff rest qvars *)
    (*       else false *)
    (*     | [] -> true *)
    (* in *)
    let () = Debug.ninfo_hprint (add_str  "sl_node.eval" string_of) e no_pos in
    let res = EQ.check_sat_over e.heap.eql_f in
    if res = Out.UNSAT then Out.UNSAT, [] else
      if bheap_only then
    (* SAT
       - if no ind preds
    *)
        if e.heap.hpreds = [] then
        (* if heap_only then *)
          EQ.check_sat e.heap.eql_f, []
            (* else *)
            (*   let p = (CP.mkAnd (EQ.to_pure e.heap.eql_f) e.arith.arith_pure no_pos) in *)
            (*   if is_sat_fnc p then *)
      (*     Out.SAT *)
      (*   else Out.UNSAT *)
        else res, []
      (* UNSAT: over and false *)
        (* if heap_only then *)
        (* let eql = EQ.mkAnd e.heap.eql_f e.heap.ho_inv_preds in *)
      else
        (*   (\* combine *\) *)
        let p = CP.mkAnd ((* CP.mkAnd (EQ.to_pure e.heap.eql_f) *) e.arith.arith_pure)  e.arith.inv_preds no_pos in
        if not (is_sat_fnc p) then
          Out.UNSAT, []
        else if e.heap.hpreds = [] then
          Out.SAT, []
        else
          Out.UNKNOWN, []

 let eval_all is_heap_only e=
   if EQ.check_sat_over e.heap.eql_f == Out.UNSAT then
     Out.UNSAT
   else
     if not is_heap_only then
       (* combine *)
       let p = CP.mkAnd (CP.mkAnd (EQ.to_pure e.heap.eql_f) e.arith.arith_pure no_pos)  e.arith.inv_preds no_pos in
       (* let () = Debug.info_hprint (add_str  "SLNODE:eval_all not heap-only" CP.string_of) p no_pos in *)
       if not (is_sat_fnc p) then
         Out.UNSAT
       else
         Out.SAT
     else
       let () = Debug.ninfo_hprint (add_str  "SLNODE:eval_all heap-only" pr_id) "xxx" no_pos in
       let p = EQ.mkAnd e.heap.eql_f e.heap.ho_inv_preds in
       EQ.check_sat p

end;;

open SL_NODE_DATA

let elim_eq_x e0 =
  let subst_one from_sv to_sv (preds, ptos,elimed_eqs)=
    if Var.equal from_sv to_sv then
      (preds, ptos,elimed_eqs)
    else
      let n_preds = List.map (CPeN.subst [(from_sv,to_sv)]) preds in
      let n_ptos = List.map (CPoN.subst [(from_sv,to_sv)]) ptos in
      let n_elimed_eqs = List.map (fun (sv1,sv2) ->
          let n_sv1 = if Var.equal sv1 from_sv then to_sv else sv1 in
          let n_sv2 = if Var.equal sv2 from_sv then to_sv else sv2 in
          (n_sv1, n_sv2)
      ) elimed_eqs in
      (n_preds, n_ptos, n_elimed_eqs)
  in
  (****************************)
  let eqs = e0.heap.eql_f.EQ.eqs in
  if eqs == [] || EQ.check_sat_over e0.heap.eql_f == Out.UNSAT then
    eqs, e0
  else begin
    let elimed_eqs0 = e0.elimed_eqs in
    (* subst eql_f *)
    let arr_eqs, elim_svs, uni_eqs, n_eql_f = EQ.elim_eq e0.heap.eql_f in
    (* if it is false. STOP *)
    let e2 =
      if not n_eql_f.EQ.is_poss_sat then
        let n_qf_eql_f = {e0.heap.qf_eql_f with EQ.is_poss_sat = false} in
        let n_ho_invp = {e0.heap.ho_inv_preds with EQ.is_poss_sat = false} in
        let nh = {e0.heap with
            qf_eql_f = n_qf_eql_f;
            eql_f = n_eql_f;
            ho_inv_preds = n_ho_invp;} in
        let e1 = {e0 with elimed_eqs = uni_eqs;
            qvars = Var.diff e0.qvars elim_svs;
            heap = nh;
        } in e1
      else
        (*subst qf_eql_f*)
        let _, _,_, n_qf_eql_f = EQ.elim_eq e0.heap.qf_eql_f in
        (* subst hpred and ptos, one by one eq *)
        let preds0 = e0.heap.hpreds in
        let ptos0 = e0.heap.hptos in
        let  (n_preds, n_ptos, n_elimed_eqs) = List.fold_left (
            fun (acc1, acc2 ,acc3) (from_sv, to_sv) ->
                subst_one from_sv to_sv (acc1, acc2 ,acc3)
        ) ( preds0, ptos0, elimed_eqs0) arr_eqs in
        let nh = {hpreds = n_preds;
        hptos = n_ptos;
        qf_eql_f = n_qf_eql_f;
        eql_f = n_eql_f;
        ho_inv_preds = e0.heap.ho_inv_preds;
        } in
        let n_a = p_subst arr_eqs e0.arith in
        let e1 = {e0 with elimed_eqs = n_elimed_eqs@uni_eqs;
            qvars = Var.diff e0.qvars elim_svs;
            heap = nh;
            arith = n_a;
        } in e1
    in
    eqs,e2
  end

let elim_eq e =
  let pr_out = pr_pair (pr_list Var.string_of_pair) SL_NODE_DATA.string_of in
  Debug.no_1 "SL_NODE.elim_eq" SL_NODE_DATA.string_of pr_out
      (fun _ -> elim_eq_x e) e

let expand_closure e=
  let eql_f = e.heap.eql_f in
  let n_eql_f = EQ.expand_closure eql_f in
  let n_h = {e.heap with eql_f = n_eql_f } in
  {e with heap = n_h}

let mk_data_x pdecls b_elim_eq f =
  let qvs, _, hp, hptos, qf_eq, eq, arith, invp, ho_invp=
    SLU.star_decompose pdecls f in
  let h = {hpreds = hp;
      hptos = hptos;
      qf_eql_f = qf_eq;
      eql_f = eq;
      ho_inv_preds = ho_invp;} in
  let a = { arith_pure = arith;
      inv_preds = invp;
  } in
  let e = {
      elimed_eqs = [];
      qvars = qvs;
      heap = h;
      arith = a;
  } in
  if b_elim_eq then
    let _, e1 = elim_eq e in
    e1
  else e

let mk_data pdecls b_elim_eq f =
  Debug.no_2 "SL_NODE.mk_data" CF.string_of string_of_bool SL_NODE_DATA.string_of
      (fun _ _ -> mk_data_x pdecls b_elim_eq f) f b_elim_eq

let mk_data_from_pure pdecls b_elim_eq p =
  let f = CF.mkBase CH.HEmp p no_pos in
  mk_data pdecls b_elim_eq f

let mkStarAnd n1 n2=
  (* disjoint of two heaps *)
  let inter_diseqs = List.fold_left (fun acc pto2->
      let inter_diseqs = List.map (fun pto1 ->
          (pto1.CPoN.hpto_node, pto2.CPoN.hpto_node)
      ) n1.heap.hptos in
      acc@inter_diseqs
  ) [] n2.heap.hptos in
  (* normalize eql_f2 *)
  let eql_f2 = EQ.mkAnd_diseqs n2.heap.eql_f inter_diseqs in
  let qf_eql_f2 = if not eql_f2.EQ.is_poss_sat then
    {n2.heap.qf_eql_f with EQ.is_poss_sat = false;}
  else
    (* EQ.mkAnd_diseqs *) n2.heap.qf_eql_f (* inter_diseqs *)
  in
  let h2 = {n2.heap with eql_f = eql_f2;
      qf_eql_f = qf_eql_f2;
  } in
  let n2 = {n2 with heap = h2;} in
  let h = { hpreds = n1.heap.hpreds@n2.heap.hpreds;
      hptos = n1.heap.hptos@n2.heap.hptos;
      qf_eql_f = EQ.mkAnd n1.heap.qf_eql_f n2.heap.qf_eql_f;
      eql_f = EQ.mkAnd n1.heap.eql_f n2.heap.eql_f;
      ho_inv_preds = EQ.mkAnd n1.heap.ho_inv_preds n2.heap.ho_inv_preds ;
  } in
  let a = {arith_pure = CP.mkAnd n1.arith.arith_pure n2.arith.arith_pure no_pos;
      inv_preds = CP.mkAnd n1.arith.inv_preds n2.arith.inv_preds no_pos;} in
  {
      elimed_eqs = n1.elimed_eqs@n2.elimed_eqs;
      qvars = Var.remove_dups (n1.qvars@n2.qvars);
      heap = h;
      arith = a;
  }

let mkStarAnd_f pdecls b_elim_eq n1 f=
  let sf1 = mk_data pdecls false f in
  let n2 = mkStarAnd n1 sf1 in
  let eqs, n3 = if b_elim_eq  then
    elim_eq n2
  else [],n2 in
  eqs, (* mkExNull *) n3

let mkStarAnd_pure pdecls b_elim_eq n p=
  let sf1 = mk_data_from_pure pdecls false p in
  let n2 = mkStarAnd n sf1 in
  let eqs, n3 =
    if b_elim_eq then elim_eq n2
    else
      [], n2
  in eqs, (* mkExNull *) n3

let unfold_bfs_x pdecls breturn_first_sat bheap_only (sf:t) : ((t * (CPeN.t * CF.t * CPeN.t list)) list)=
  let rec select_hpred ptos (fst, tl) preds rem=
    match preds with
      | vn::rest ->
            let srcs = Cpred.get_root_src_composition pdecls vn.CPeN.hpred_name  vn.CPeN.hpred_arguments in
          if (Var.intersect srcs ptos) != [] then
            vn, (rem@rest)
          else select_hpred ptos (fst, tl) rest (rem@[vn])
      | [] -> (fst, tl)
  in
  (*********************)
  let remove_redundant_ex_qvars e0=
    if bheap_only && e0.heap.hptos == [] && List.length e0.qvars >4 then
      (* remove no longer used ex qvars *)
      let () = Debug.ninfo_hprint (add_str  "remove no longer used ex qvars" SL_NODE_DATA.string_of_short) e0 no_pos in
      let used_svs = List.fold_left (fun r hpred ->
          r@hpred.CPeN.hpred_arguments
      ) [] e0.heap.hpreds in
      let used_qvars, unused_qvars = List.partition (fun v->
          Var.mem v used_svs
      ) e0.qvars in
      let () = Debug.ninfo_hprint (add_str  "remove no longer used ex qvars" Var.string_of_list) unused_qvars no_pos in
      let _, n_eql_f = EQ.elim_ex_qvars unused_qvars e0.heap.eql_f in
      let n_heap = {e0.heap with eql_f = n_eql_f} in
      {e0 with qvars = used_qvars;
          heap = n_heap;
      }
    else e0
  in
  (*********************)
  if sf.heap.hpreds == [] then
    []
  else
    (* breadth first sorted *)
    let sorted_hpreds = List.sort CPeN.bfs_cmp sf.heap.hpreds in
    let fst_hpred, tl_hpred = match sorted_hpreds with
      | x::tl -> x, tl
      | [] -> raise Not_found
    in
    let selected_pred, remaining_hpreds =
      if sf.heap.hptos == [] || (not !VarGen.sat_allow_breadth_reorder) then
         fst_hpred, tl_hpred
      else
        let u = fst_hpred.CPeN.hpred_unfold_num in
        let sel_hpreds, rem_hpreds = List.partition (fun vn ->
            vn.CPeN.hpred_unfold_num == u
        ) sf.heap.hpreds in
        select_hpred (List.map (fun dn -> dn.CPoN.hpto_node) sf.heap.hptos) (fst_hpred, tl_hpred) sel_hpreds []
    in
    let nh = {sf.heap with hpreds = remaining_hpreds} in
    let n_sf = {sf with heap = nh} in
    (* look up pred definition *)
    let pred_defn = List.find (fun decl -> Ustr.str_eq decl.Cpred.pred_name selected_pred.CPeN.hpred_name) pdecls in
    (* rename act/formal parameter and refresh qvars *)
    let sst = List.combine pred_defn.Cpred.pred_vars selected_pred.CPeN.hpred_arguments in
    (********************)
    let mkAnd_one_br f = begin
      let nf = match f with
        | CF.Base fb -> let fb1 = CSH.subst sst fb in
          CF.Exists (fb1, sf.qvars)
        | CF.Exists (fb, qvars) ->
              let n_qvars = Var.fresh_vars qvars in
              let sst2 = List.combine qvars n_qvars in
              CF.Exists (CSH.subst (sst@sst2) fb, (sf.qvars@n_qvars))
        | _ -> failwith "sl_node.unfold_bfs: disj can not happen"
      in
      let sf1 = mk_data pdecls false nf in
      (* update unfold_num *)
      let sub_views = List.map (fun v ->
          {v with CPeN.hpred_unfold_num = selected_pred.CPeN.hpred_unfold_num + v.CPeN.hpred_unfold_step;}
      ) sf1.heap.hpreds in
      let h1 = {sf1.heap with hpreds = sub_views} in
      (****************)
      let sf0 = {sf1 with heap = h1} in
      let f0 = (selected_pred, nf, sub_views) in
      let eql1 = mkStarAnd n_sf sf0 in
      let _, eql = elim_eq eql1 in
      let unfold_lbls = Cpred.search_pred_base_linear_unfold
        pdecls eql.heap.hpreds eql.heap.eql_f.EQ.eqs eql.heap.eql_f.EQ.null_vars in
      match unfold_lbls with
          | [(sub_vn, sub_br)] ->
                let nf1 = CF.mkStarAnd sub_br (CF.subtract_pred nf sub_vn) in
                let sub_views1 = List.filter (fun vn1 -> not(CPeN.equal vn1 sub_vn)) eql.heap.hpreds  in
                let n_h1 = {eql.heap with hpreds = sub_views1} in
                let _, n_eql = mkStarAnd_f pdecls false ({eql with heap = n_h1}) sub_br  in
                let f1 = (selected_pred, nf1, sub_views1) in
                (n_eql, f1)
          | _ -> eql,f0
    end
    in
    let rec fold_left_return_first fs res=
      match fs with
        | f::rest ->
              (* let () = Debug.info_hprint (add_str  "f" CF.string_of) f no_pos in *)
              let eql,f0 = mkAnd_one_br f in
              let r, _ =
                (* EQ.check_sat_over eql.heap.eql_f *)
                    eval pdecls bheap_only [] eql
              in
              if r == Out.UNSAT then
                fold_left_return_first rest res
              else begin
                if eql.heap.hpreds ==[] then [(eql, f0)]
                else
                  let eql1 = remove_redundant_ex_qvars eql in
                  fold_left_return_first rest (res@[(eql1, f0)])
              end
        | [] -> res
    in
    (********************)
    let brs = (CF.list_of_disjuncts pred_defn.Cpred.pred_formula) in
    if breturn_first_sat then
      fold_left_return_first brs []
    else
      List.fold_left (fun r f ->
          let eql2,f0 = mkAnd_one_br f in
          (* let () = Debug.info_hprint (add_str  "slNode:eql2" string_of) eql2 no_pos in *)
          if EQ.check_sat_over eql2.heap.eql_f == Out.UNSAT then
            r
          else
            let eql1 = remove_redundant_ex_qvars eql2 in
             (* let () = Debug.info_hprint (add_str  "slNode:eql1" string_of) eql1 no_pos in *)
            r@[(eql1, f0)]
      ) [] brs

let unfold_bfs pdecls breturn_first_sat bheap_only (sf:t)=
  let pr1 = string_of_short in
  let pr2 = string_of_bool in
  let pr3 = pr_pair pr1 (pr_triple CPeN.string_of CF.string_of (pr_list CPeN.string_of)) in
  let pr_out = pr_list_ln pr3 in
  Debug.no_3 "unfold_bfs" pr2 pr2 pr1 pr_out
      (fun _ _ _ -> unfold_bfs_x pdecls breturn_first_sat bheap_only (sf:t))  breturn_first_sat bheap_only sf

 let get_univ_ptos_x e=
   let ptrs = List.fold_left (fun acc pto ->
       if not (Var.mem pto.CPoN.hpto_node e.qvars) then
         acc@[pto.CPoN.hpto_node]
       else acc
       ) [] e.heap.hptos in
   Var.get_eq_closure e.heap.eql_f.EQ.eqs ptrs

 let get_univ_ptos e=
   Debug.no_1 "get_univ_ptos" string_of Var.string_of_list
       (fun _ -> get_univ_ptos_x e) e

 let get_node_arith e=
   e.arith.arith_pure

 let is_base_node e=
   e.heap.hpreds == []

 let get_univ_preds_x e=
   e.qvars, e.heap.hpreds, List.fold_left (fun acc view ->
       if (Var.diff view.CPeN.hpred_arguments e.qvars) != [] then
         acc@[view]
       else acc
       ) [] e.heap.hpreds

 let get_univ_preds e=
   Debug.no_1 "get_univ_preds" string_of
       (pr_triple Var.string_of_list (pr_list CPeN.string_of) (pr_list CPeN.string_of))
       (fun _ -> get_univ_preds_x e) e

(*
  presume that views in both comp and bud are quantified
*)
 let is_quantified_subsumed_views_x bud comp=
   let rec aux_match comp_vns bud_vns sst=
     match comp_vns with
       | cvn::rest -> begin
           let same_bvns, rem = List.partition (fun bvn ->
               Ustr.str_eq cvn.CPeN.hpred_name bvn.CPeN.hpred_name
           ) bud_vns in
           match same_bvns with
             | bvn::rem2 ->
                   let n_sst = List.combine cvn.CPeN.hpred_arguments
                     bvn.CPeN.hpred_arguments in
                   aux_match rest (rem@rem2) (sst@n_sst)
             | [] -> false, sst
         end
       | [] -> true,sst
   in
   let comp_vns = comp.heap.hpreds in
   let bud_vns = bud.heap.hpreds in
   let is_match, sst = aux_match comp_vns bud_vns [] in
   if is_match then
     let interest_vs = Var.remove_dups (List.map fst sst) in
     let comp_neqnull_vs = Var.intersect interest_vs comp.heap.eql_f.EQ.disnull_vars  in
     let require_bud_neqnull_vs = List.map (Var.subst sst) comp_neqnull_vs in
     let bud_neqnull_vs = bud.heap.eql_f.EQ.disnull_vars in
     if List.for_all (fun v1 -> Var.mem v1 bud_neqnull_vs) require_bud_neqnull_vs then
       begin
         (* let comp_null_vs = Var.intersect interest_vs comp.heap.eql_f.EQ.null_vars  in *)
         (* let require_bud_null_vs = List.map (Var.subst sst) comp_null_vs in *)
         (* let bud_null_vs = bud.heap.eql_f.EQ.null_vars in *)
         (* if List.for_all (fun v1 -> Var.mem v1 bud_null_vs) require_bud_null_vs then *)
         (*   true *)
         (* else *)
         (*   false *)
         true
       end
     else
       false
   else
     false

let is_quantified_subsumed_views bud comp=
  let pr1 = string_of in
  Debug.no_2 "is_quantified_subsumed_views" pr1 pr1 string_of_bool
      (fun _ _ -> is_quantified_subsumed_views_x bud comp) bud comp

let qf_equal_x (* is_qf *) d1 d2=
   (* if is_qf then *)
     EQ.eq d1.heap.qf_eql_f d2.heap.qf_eql_f
   (* else *)
     (* EQ.eq d1.heap.eql_f d2.heap.eql_f *)
   (* EQ.check_sat (EQ.mkAnd d1.heap.eql_f d2.heap.eql_f) == Out.SAT *)

let qf_equal d1 d2=
  let pr =  string_of in
  Debug.no_2 "qf_equal" pr pr string_of_bool
      (fun _ _ -> qf_equal_x d1 d2) d1 d2

(* all views are quantified and disjoint *)
 let syntax_complete_bud d=
   let rec is_inter_ls ls_args=
     match ls_args with
       | x::tl -> if List.exists (fun y -> Var.intersect x y != []) tl then true
         else is_inter_ls tl
       | [] -> false
   in
   let closure_ls_args = List.map (fun view -> Var.get_eq_closure d.heap.eql_f.EQ.eqs view.CPeN.hpred_arguments) d.heap.hpreds in
   not (is_inter_ls closure_ls_args)

(*
 computing bases of preds
  for entail, we find bases of bud also (NO but discard pred)
*)
let star_compose_univ_x (* is_bud *) e=
   let ptos = List.fold_left (fun r p ->
       CH.mkStarAnd r (CH.PtoNode p) no_pos
   ) CH.HEmp e.heap.hptos in
   let h = (* if is_bud then ptos else *)
     List.fold_left (fun r v ->
         CH.mkStarAnd r (CH.PredNode v) no_pos
     ) ptos ((* List.filter (fun vn -> Var.diff vn.CPeN.hpred_arguments e.qvars != []) *) e.heap.hpreds) in
    (* with uni eliminated equalities *)
   let p0 = List.fold_left (fun acc_p (sv1, sv2) ->
       let p = CP.mkEqExp (Exp.mkVar sv1 no_pos) (Exp.mkVar sv2 no_pos) no_pos in
       CP.mkAnd acc_p p no_pos
   ) (CP.mkTrue no_pos) e.elimed_eqs in
   let p = CP.mkAnd (CP.mkAnd p0 (EQ.to_pure e.heap.eql_f) no_pos)(CP.mkAnd e.arith.inv_preds e.arith.arith_pure no_pos) no_pos in
   let sst, subst_qvars = List.fold_left (fun (r1,r2) (v1,v2) ->
       if Var.mem v1 e.qvars then
         (r1@[(v1,v2)],r2@[v1])
       else if Var.mem v2 e.qvars then
          (r1@[(v2,v1)],r2@[v2])
       else (r1,r2)
   ) ([],[]) e.heap.eql_f.EQ.eqs in
   let new_h = Cheap.h_subst sst h in
   let new_p = CP.subst_var sst p in
   let qvars = (Var.diff e.qvars (Var.remove_dups subst_qvars)) in
   let bare = CF.mkBase new_h new_p no_pos in
   if qvars = [] then
     bare
   else CF.add_quantifiers qvars bare

let star_compose_univ (* is_bud *) e=
  let pr1 = string_of in
  let pr2 = CF.string_of in
  Debug.no_1 "SLNODE.star_compose_univ" pr1 pr2
      (fun _ -> star_compose_univ_x (* is_bud *) e)
      (* is_bud *) e

let star_compose_x e=
   let ptos = List.fold_left (fun r p ->
       CH.mkStarAnd r (CH.PtoNode p) no_pos
   ) CH.HEmp e.heap.hptos in
   let h = List.fold_left (fun r v ->
         CH.mkStarAnd r (CH.PredNode v) no_pos
     ) ptos e.heap.hpreds in
    (* with uni eliminated equalities *)
   (* let p0 = List.fold_left (fun acc_p (sv1, sv2) -> *)
   (*     let p = CP.mkEqExp (Exp.mkVar sv1 no_pos) (Exp.mkVar sv2 no_pos) no_pos in *)
   (*     CP.mkAnd acc_p p no_pos *)
   (* ) (CP.mkTrue no_pos) e.elimed_eqs in *)
   let p0 = (CP.mkTrue no_pos) in
   let p = CP.mkAnd (CP.mkAnd p0 (EQ.to_pure e.heap.eql_f) no_pos)(CP.mkAnd e.arith.inv_preds e.arith.arith_pure no_pos) no_pos in
   let bare = CF.mkBase h p no_pos in
   let qvars = e.qvars in
   if qvars = [] then
     bare
   else CF.add_quantifiers qvars bare

let star_compose e=
  let pr1 = string_of in
  let pr2 = CF.string_of in
  Debug.no_1 "SLNODE.star_compose" pr1 pr2
      (fun _ -> star_compose_x e) e

let string_of_pretty e =
  let f = star_compose e in
  CF.string_of f

let equal e1 e2=
  let f1 = star_compose e1 in
  let f2 = star_compose e2 in
  CF.equal f1 f2

let star_decompose e=
  (e.qvars, e.heap.hpreds, e.heap.hptos, e.heap.eql_f, e.arith.arith_pure)

module SLNODE = Node.FNode(SL_NODE_DATA)

