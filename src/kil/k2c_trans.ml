open Globals
open Ustr
open VarGen
open Gen
open Gen.Basic
open Error

module TI = Typeinf

module IF = Iformula
module ISH = Isymheap
module IP = Ipure
module IT = Iterm
module IE = Iexp
module IH = Iheap
module IHN = IheapNode

module CF = Cformula
module CB = Csymheap
module CP = Cpure
module CT = Term
module CE = Exp
module CH = Cheap
module CPN = CpredNode

let trans_var_safe (ve, pe) et tlist pos=
  if (ve.[0] = '#') then Var.mk UNK "_3_" Unprimed
  else try
    let ve_info = snd(List.find (fun (v,en)->v=ve) tlist)
    in
    (match ve_info.TI.sv_info_kind with
      | UNK -> Var.mk et ve pe
      | t -> Var.mk t ve pe
    )
  with Not_found -> Var.mk et ve pe

let trans_var_x (ve, pe) (tlist: TI.var_type_list) pos : Var.t=
  if (ve.[0] = '#') then
    Var.mk UNK "_2_" Unprimed
  else try
    let ve_info = snd (List.find (fun (v,en)-> Ustr.str_eq v ve) tlist) in
    (match ve_info.TI.sv_info_kind with
      | t -> Var.mk t ve pe
    )
  with Not_found -> Var.mk UNK ve pe

let trans_var (ve, pe) (tlist: TI.var_type_list) pos : Var.t=
  let pr1 = TI.string_of_tlist in
  let pr2 = Var.string_of_full in
  let pr3 (id, _) = pr_id id in
  Debug.no_2 "trans_var" pr3 pr1 pr2
      (fun _ _ -> trans_var_x (ve, pe) tlist pos) (ve, pe) tlist

let match_exp tlist (hargs : Iexp.t list) : (Var.t list) =
  let pos = no_pos in
  let rec aux hargs res=
    match hargs with
      | e :: rest ->
            let str = (Iexp.string_of e) in
            let e_hvars = match e with
              | Iexp.Var ((ve, pe), pos_e) -> [(trans_var_safe (ve, pe) UNK tlist pos_e)]
              | _ ->  Gen.report_error pos ("malfunction with float out exp: "^str) in
            aux rest (res@e_hvars)
      | [] -> res
  in
  aux hargs []

let rec trans_exp (e00 : Iexp.t) (tlist: TI.var_type_list) : Exp.t =
  let rec helper e0=
    match e0 with
      | IE.Null pos -> CE.Null pos
      | IE.Var ((v, p), pos) -> CE.Var ((trans_var (v,p) tlist pos),pos)
      | IE.Ann_Exp (e, t, pos) -> helper e
      | IE.IConst (c, pos) -> CE.IConst (c, pos)
      | IE.FConst (c, pos) -> CE.FConst (c, pos)
      | IE.CConst (c, pos) -> CE.CConst (c, pos)
      | IE.SConst (c, pos) -> CE.SConst (c, pos)
      | IE.Add (e1, e2, pos) -> CE.Add (helper e1, helper e2, pos)
      | IE.Subtract (e1, e2, pos) -> CE.Subtract (helper e1, helper e2, pos)
      | IE.Mult (e1, e2, pos) -> CE.Mult (helper e1, helper e2, pos)
      | IE.Div (e1, e2, pos) -> CE.Div (helper e1, helper e2, pos)
      | IE.Max (e1, e2, pos) -> CE.Max (helper e1, helper e2, pos)
      | IE.Min (e1, e2, pos) -> CE.Min (helper e1, helper e2, pos)
      | IE.TypeCast (ty, e1, pos) -> CE.TypeCast (ty, helper e1, pos)
      | IE.Bag (elist, pos) -> CE.Bag (trans_exp_list elist tlist, pos)
      | IE.BagUnion (elist, pos) -> CE.BagUnion (trans_exp_list elist tlist, pos)
      | IE.BagIntersect (elist, pos) -> CE.BagIntersect (trans_exp_list elist tlist, pos)
      | IE.BagDiff (e1, e2, pos) -> CE.BagDiff (helper e1, helper e2, pos)
      | IE.ArrayAt ((a, p), ind, pos) ->
            let cpind = List.map (fun i -> helper i) ind in
            let dim = List.length ind in
            (* currently only support int type array *)
            CE.ArrayAt ((Var.mk (Array (int_type, dim)) a p), cpind, pos)
      | IE.Concat (e1, e2, pos) -> CE.Concat (helper e1, helper e2, pos)
  in helper e00

and trans_exp_list (elist : IE.t list) (tlist: TI.var_type_list): Exp.t list =
  let rec helper el res=
    match el with
      | [] -> res
      | e :: rest -> helper rest (res@[(trans_exp e tlist)])
  in helper elist []


let trans_term (pf : Iterm.t) (tlist: TI.var_type_list) : Term.t=
  let rec helper pf = match pf with
    | IT.BConst (b, pos) -> CT.BConst (b, pos)
    | IT.BVar ((v, p), pos) -> CT.BVar (Var.mk bool_type v p, pos)
    | IT.Lt (e1, e2, pos) ->
          let pe1 = trans_exp e1 tlist in
          let pe2 = trans_exp e2 tlist in CT.mkLt pe1 pe2 pos
    | IT.Lte (e1, e2, pos) ->
          let pe1 = trans_exp e1 tlist in
          let pe2 = trans_exp e2 tlist in CT.mkLte pe1 pe2 pos
    | IT.Gt (e1, e2, pos) ->
          let pe1 = trans_exp e1 tlist in
          let pe2 = trans_exp e2 tlist in CT.mkGt pe1 pe2 pos
    | IT.Gte (e1, e2, pos) ->
          let pe1 = trans_exp e1 tlist in
          let pe2 = trans_exp e2 tlist in CT.mkGte pe1 pe2 pos
    | IT.Eq (e1, e2, pos) ->
          let pe1 = trans_exp e1 tlist in
          let pe2 = trans_exp e2 tlist in
          (CT.mkEq pe1 pe2 pos)
    | IT.Neq (e1, e2, pos) ->
          let pe1 = trans_exp e1 tlist in
          let pe2 = trans_exp e2 tlist in CT.mkNeq pe1 pe2 pos
    | IT.EqMax (e1, e2, e3, pos) ->
          let pe1 = trans_exp e1 tlist in
          let pe2 = trans_exp e2 tlist in
          let pe3 = trans_exp e3 tlist in CT.EqMax (pe1, pe2, pe3, pos)
    | IT.EqMin (e1, e2, e3, pos) ->
          let pe1 = trans_exp e1 tlist in
          let pe2 = trans_exp e2 tlist in
          let pe3 = trans_exp e3 tlist in CT.EqMin (pe1, pe2, pe3, pos)
    | IT.BagIn ((v, p), e, pos) ->
          let pe = trans_exp e tlist in CT.BagIn ((trans_var (v,p) tlist pos), pe, pos)
    | IT.BagNotIn ((v, p), e, pos) ->
          let pe = trans_exp e tlist in
          CT.BagNotIn ((trans_var (v,p) tlist pos), pe, pos)
    | IT.BagSub (e1, e2, pos) ->
          let pe1 = trans_exp e1 tlist in
          let pe2 = trans_exp e2 tlist in CT.BagSub (pe1, pe2, pos)
    | IT.BagMax ((v1, p1), (v2, p2), pos) ->
          CT.BagMax ((Var.mk int_type v1 p1), Var.mk bag_type v2 p2, pos)
    | IT.BagMin ((v1, p1), (v2, p2), pos) ->
          CT.BagMin (Var.mk int_type v1 p1, Var.mk bag_type v2 p2, pos)
    | IT.RelForm (r, args, pos) ->
          (* let nv = trans_var_safe (r,Unprimed) (RelT[]) tlist pos in *)
          (* Match types of arguments with relation signature *)
          let cpargs = trans_exp_list args tlist in
          CT.RelForm (r, cpargs, pos)
  in
  let npf = helper pf in
  npf

let rec trans_pure_formula (f0 : IP.t) (tlist: TI.var_type_list) : CP.t =
  match f0 with
    | IP.BForm it -> CP.BForm (trans_term it tlist)
    | IP.And (f1, f2, pos) ->
          let pf1 = trans_pure_formula f1 tlist in
          let pf2 = trans_pure_formula f2 tlist in
          CP.mkAnd pf1 pf2 pos
    | IP.Or (f1, f2, pos) ->
          let pf1 = trans_pure_formula f1 tlist in
          let pf2 = trans_pure_formula f2 tlist in
          CP.mkOr pf1 pf2 pos
    | IP.Not (f, pos) ->
          let pf = trans_pure_formula f tlist in
          CP.mkNot pf pos
    | IP.Forall ((v, p), f, pos) ->
          let pf =  trans_pure_formula f tlist in
          let v_type = Var.type_of
            (trans_var (v,Unprimed) tlist pos) in
          let sv = Var.mk v_type v p in
          CP.mkForall [sv] pf pos
    | IP.Exists ((v, p), f, pos) ->
          let pf = trans_pure_formula f tlist in
          let sv = trans_var (v,p) tlist pos in
          CP.mkExists [sv] pf pos

let expand_dereference_node (f: IH.t) pos : (IH.t * (Globals.ident * VarGen.primed) list) =
  let rec acc_helper i n p1 new_vars s dr l heaps=
    if i>n then
      (p1, new_vars, s, heaps)
    else
      let p2 = IE.mkVar p1 l in
      let fresh_var = "deref_" ^ (fresh_name ()) in
      let new_vars = new_vars @ [(fresh_var, Unprimed)] in
      let p1 = (fresh_var, Unprimed) in
      let s = s ^ "_star" in
      let h = IH.mkPtoNode p1 s 0 dr [p2] l in
      let heaps = heaps @ [h] in
      acc_helper (i+1) n p1 new_vars s dr l heaps
  in
  match f with
    | IH.PtoNode {IHN.heap_node = n;
      IHN.heap_name = c;
      IHN.heap_deref = deref;
      IHN.heap_derv = dr;
      IHN.heap_arguments = exps;
      IHN.heap_pos = l;
      } -> begin
        if (c = generic_pointer_type_name) then
          Gen.report_error l "expand_dereference_node: unexpected generic pointer"
        else if (deref > 0) then (
            let base_heap_id = c in
            let expanded_heap, newvars = (
                match base_heap_id with
                  | "int"
                  | "bool"
                  | "float"
                  | "void" -> (
                        (* dereference to a basic type *)
                        if (deref = 1) then (
                            let base_heap_id = base_heap_id ^ "_star" in
                            let hf = IH.mkPtoNode n base_heap_id 0 dr exps l in
                            (hf, [])
                        )
                        else (
                            let base_heap_id = base_heap_id ^ "_star" in
                            let s = base_heap_id in
                            let fresh_var = "deref_" ^ (fresh_name ()) in
                            let new_vars = [(fresh_var, Unprimed)] in
                            let p = (fresh_var, Unprimed) in
                            let p1 = p in
                            (* let p2 = ref (IF.P.Var (("", Unprimed), l)) in *)
                            (* let heaps = ref [] in *)
                            let (p1, new_vars, s, heaps) = acc_helper 3 deref p1 new_vars s dr l [] in
                            (* for i = 3 to deref do *)
                            (*   p2 := IF.P.Var (!p1, l); *)
                            (*     let fresh_var = "deref_" ^ (fresh_name ()) in *)
                            (*     new_vars := !new_vars @ [(fresh_var, Unprimed)]; *)
                            (*     p1 := (fresh_var, Unprimed); *)
                            (*     s := !s ^ "_star"; *)
                            (*     let h = IF.mkHeapNode !p1 !s ho_exps 0 dr split imm inv full pd perm [!p2] ann_param None l in *)
                            (*     heaps := !heaps @ [h]; *)
                            (* done; *)
                            let s = s ^ "_star" in
                            let e = IE.mkVar p1 l in
                            let h1 = IH.mkPtoNode n s 0 dr [e] l in
                            let h2 = IH.mkPtoNode p base_heap_id 0 dr (exps) l in
                            let hf = List.fold_left (fun f1 f2 -> IH.mkStar f1 f2 l) h1 (heaps @ [h2]) in
                            (hf, new_vars)
                        )
                    )
                  | _ -> (
                        (* dereference to a data structure *)
                        (* let new_vars = [] in *)
                        let s =  base_heap_id in
                        let fresh_var = "deref_" ^ (fresh_name ()) in
                        let new_vars = [(fresh_var, Unprimed)] in
                        let p = (fresh_var, Unprimed) in
                        let p1 = p in
                        (* let p2 = ref (IF.P.Var (("", Unprimed), l)) in *)
                        (* let heaps =  [] in *)
                        let (p1, new_vars, s, heaps) = acc_helper 2 deref p1 new_vars s dr l [] in
                        (* for i = 2 to deref do *)
                        (*   p2 := IF.P.Var (!p1, l); *)
                        (*     let fresh_var = "deref_" ^ (fresh_name ()) in *)
                        (*     new_vars := !new_vars @ [(fresh_var, Unprimed)]; *)
                        (*     p1 := (fresh_var, Unprimed); *)
                        (*     s := !s ^ "_star"; *)
                        (*     let h = IF.mkHeapNode !p1 !s ho_exps 0 dr split imm full inv pd perm [!p2] ann_param None l in *)
                        (*     heaps := !heaps @ [h]; *)
                        (* done; *)
                        let s = s ^ "_star" in
                        let e = IE.mkVar p1 l in
                        let offe = IE.mkVar ("o", Unprimed) l in
                        let h1 = IH.mkPtoNode n s 0 dr [e;offe] l in
                        let h2 = IH.mkPtoNode p c 0 dr (exps) l in
                        let hf = List.fold_left (fun f1 f2 -> IH.mkStar f1 f2 l) h1 (heaps @ [h2]) in
                        (hf, new_vars)
                    )
            ) in
            (* return *)
            (expanded_heap, newvars)
        )
        else
          Gen.report_error l "expand_dereference_node: expect a dereference HeapNode"
      end
    | _ -> Gen.report_error pos "expand_dereference_node: expect a PtoNode"

let trans_heap ddecls pdecls rdecls (h0 : IH.t) (pos : VarGen.loc) (tl0: TI.var_type_list):
      (CH.t * (Globals.ident * VarGen.primed) list * (TI.var_type_list)) =
  let rec helper f tl=
    match f with
      | IH.HeapNode2 h2 -> Gen.report_error pos "malfunction with convert to heap node"
      | IH.PredNode {
        IHN.hpred_name = c;
        IHN.hpred_deref = deref;
        IHN.hpred_derv = dr;
        IHN.hpred_arguments = exps;
        IHN.hpred_pos = pos;
        } ->
            let new_h = CH.PredNode (CPN.mk c dr (match_exp tl exps) pos )
            in (new_h, [], tl)
      | IH.PtoNode {IHN.heap_node = (v, p);
        IHN.heap_name = c;
        IHN.heap_deref = deref;
        IHN.heap_derv = dr;
        IHN.heap_arguments = exps;
        IHN.heap_pos = pos;
        } ->
            (* expand the dereference heap node first *)
            if (deref > 0) then (
                let (f1, newvars1) = expand_dereference_node f pos in
                let n_tl = TI.gather_type_info_heap ddecls pdecls f1 tl in
                let hf, newvars2, n_tl = helper f1 n_tl in
                (hf, newvars1 @ newvars2, n_tl)
            )
            else (
                (* ASSUMPTIONS: exps ARE ALL VARIABLES
                   i.e. I.Var AFTER float_out_exp PRE-PROCESSING! *)
          if (c = generic_pointer_type_name || String.contains v '.') then (
              let tokens = Str.split (Str.regexp "\\.") v in
              let field_access_seq = List.filter (fun x -> Inode.is_not_data_type_identifier ddecls x) tokens in
              let field_access_seq = List.tl field_access_seq in
              (* get rid of the root pointer as well *)
              let rootptr = List.hd tokens in
              let rpsi = snd (List.find(fun (v,en)->v=rootptr) tl) in
              let rootptr_type = rpsi.TI.sv_info_kind in
              let rootptr_type_name = match rootptr_type with
                | Named c1 -> c1
                | _ -> failwith ("[trans_heap] " ^ rootptr ^ " must be a pointer.")
              in
              let rootptr, p =
                let rl = String.length rootptr in
                if rootptr.[rl-1] = '\'' then
                  (String.sub rootptr 0 (rl - 1), Primed)
                else
                  (rootptr, Unprimed) in
              let field_offset = Inode.compute_field_seq_offset ddecls rootptr_type_name field_access_seq in
              let num_ptrs = Inode.compute_typ_size ddecls rootptr_type in
              (* The rest are copied from the original code with modification to account for the holes *)
              let hvars = match_exp tl exps in
              (* [Internal] Create a list [x,x+1,...,x+n-1] *)
              let rec first_naturals n x =
                if n = 0 then []
                else x :: (first_naturals (n-1) (x+1)) in
              (* Extends hvars with holes and collect the list of holes! *)
              let rec extend_and_collect_holes vs offset num_ptrs = (
                  let temp = first_naturals num_ptrs 0 in
                  let numargs = List.length vs in
                  let holes = List.fold_left (fun l i ->
                      let d = i - offset in
                      if (d < 0 || d >= numargs) then List.append l [i] else l
                  ) [] temp in
                  let () = Debug.ninfo_hprint (add_str "holes" (pr_list string_of_int)) holes no_pos in
                  let () = Debug.ninfo_hprint (add_str "vs" (Var.string_of_list)) vs no_pos in
                  let () = Debug.ninfo_hprint (add_str "offset" string_of_int) offset no_pos in
                  let newvs = List.map (fun i ->
                      if (List.mem i holes) then
                        Var.mk UNK (qvar_id ^ fresh_trailer()) Unprimed
                      else List.nth vs (i - offset)
                  ) temp in
                  (newvs,holes)
              ) in
            (* [Internal] End of function <extend_and_collect_holes> *)
            let hvars, holes = extend_and_collect_holes hvars field_offset num_ptrs in
            let all_fields = Inode.look_up_all_fields_cname ddecls rootptr_type_name in
            let comb = Debug.catch_exc "astsimpl: hvars & all_fields" (List.combine hvars) all_fields in
            let hvars = List.map (fun (sv,((t,_),_)) -> Var.mk t sv.Var.id sv.Var.p) comb in
            let () = Debug.ninfo_hprint (add_str "hvars" (pr_list Var.string_of)) hvars no_pos in
            let new_v = Var.mk rootptr_type rootptr p in
            let cheap = CH.mkPtoNode new_v hvars rootptr_type_name dr  [] pos in
            (cheap, [], tl)
          )
          else (
            (* Not a field access *)
              let hvars = match_exp tl exps in
              let new_v = Var.mk (Named c)  v p in
              let rec collect_holes vars n = (match vars with
                | [] -> []
                | x::t -> (
                      let th = collect_holes t (n+1) in
                      let vn = x.Var.id in
                      if (vn.[0] = '#') then n::th else th
                  )
              ) in
              let holes = collect_holes hvars 0 in
              let new_h = CH.mkPtoNode new_v hvars c dr holes pos in
              (new_h, [], tl)
          )
        )
      | IH.Star (f1, f2, pos) ->
        let (lf1, newvars1, n_tl) = helper f1 tl in
        let (lf2, newvars2, n_tl) = helper f2 n_tl in
        let tmp_h = CH.mkStarAnd lf1 lf2 pos in
        (tmp_h, newvars1 @ newvars2, n_tl)
      | IH.HTrue ->  (CH.HTrue, [], tl)
      | IH.HFalse -> (CH.HFalse, [], tl)
      | IH.HEmp -> (CH.HEmp, [], tl)
    in
    helper h0 tl0

let trans_base ddecls pdecls rdecls base (tl: TI.var_type_list)=
  let h = base.ISH.base_heap in
  let p = base.ISH.base_pure in
  let pos = base.ISH.base_pos in
  let (new_h, newvars1, n_tl) = trans_heap ddecls pdecls rdecls h pos tl in
  let new_p = trans_pure_formula p n_tl in
  let () = Debug.ninfo_hprint (add_str "trans_base: pure" CP.string_of) new_p pos in
  let new_p = Cpure.arith_simplify new_p in
  let () = Debug.ninfo_hprint (add_str "trans_base: simplified pure" CP.string_of) new_p pos in
  (new_h, new_p, newvars1, n_tl)

let rec trans_formula ddecls pdecls rdecls (f0: IF.t) (fvars0 : TI.var_type_list) : (TI.var_type_list * CF.t * (Globals.ident * VarGen.primed) list) =
  let rec helper f fvars=
  match f with
    | IF.Or (f1, f2, pos) ->
          let (n_tl, f1, newvars1) = helper f1 fvars in
          let (n_tl, f2, newvars2) = helper f2 n_tl in
          let cf = CF.mkOr f1 f2 pos in
          (n_tl, cf, newvars1 @ newvars2)
    | IF.Base fb -> let pos = fb.ISH.base_pos in
      let nh,np,newvars,n_tl = (trans_base ddecls pdecls rdecls fb fvars) in
      (n_tl, CF.mkBase nh np pos, newvars)
    | IF.Exists (fb, qvars) -> let pos = fb.ISH.base_pos in
      let nh,np,newvars,n_tl = (trans_base ddecls pdecls rdecls fb fvars) in
      let qvars = qvars @ newvars in
      (n_tl, CF.mkExists (List.map (fun c-> trans_var_safe c UNK fvars pos) qvars) nh np pos, [])
  in
  helper f0 fvars0

let rec trans_disj_formula (ddecls: Inode.t list) pdecls rdecls sep_collect (fvars : ident list) (f0 : IF.t) tlist: (TI.var_type_list * CF.formula) =
  let rec helper f tl =
    match f with
      | IF.Or (f1, f2, pos)->
            if IF.is_empty_heap f1 then
              let (n_tl1,n_f2)= helper f2 tl in
              let (n_tl,n_f1) = helper f1 n_tl1 in
              (n_tl, CF.mkOr n_f1 n_f2 pos)
            else
              let (n_tl1,n_f1)= helper f1 tl in
              let (n_tl,n_f2) = helper f2 n_tl1 in
              (n_tl, CF.mkOr n_f1 n_f2 pos)
      | IF.Base fb ->(
            let n_tl =
              if sep_collect then
                let n_tl = TI.gather_type_info_pure rdecls fb.ISH.base_pure tl in
                TI.gather_type_info_heap  ddecls pdecls fb.ISH.base_heap n_tl
              else tlist
            in
            let (n_tl,ch, _) =  trans_formula ddecls pdecls rdecls f n_tl in
            (n_tl, ch))
      | IF.Exists (f1, qvars)  ->
            let n_tl = (
                if sep_collect then
                  let n_tl = TI.gather_type_info_pure rdecls f1.ISH.base_pure tl in
                  TI.gather_type_info_heap ddecls pdecls f1.ISH.base_heap n_tl
                  else tl
            ) in
            let (n_tl,ch, newvars) = trans_formula ddecls pdecls rdecls (IF.Base f1) n_tl in
            let pos = f1.ISH.base_pos in
            let qsvars = List.map (fun qv -> trans_var qv n_tl pos) qvars in
            let newvars = List.map (fun qv -> trans_var qv n_tl pos) newvars in
            let ch = CF.push_exists (qsvars @ newvars) ch in
            (n_tl, ch)
  in
  let n_tl, f = helper f0 tlist in
  n_tl, TI.synchronize f n_tl

(* convert HeapNode2 to HeapNode *)
let rec h_convert_heap2 ddecls (h0 : IH.t) : IH.t =
  let rec helper h= match h with
    |IH.Star ( h1, h2, pos)
      -> let tmp1 = helper  h1 in
      let tmp2 = helper h2 in
      IH.Star (tmp1, tmp2, pos)
    | IH.HeapNode2 h2 -> IH.PtoNode (IHN.node2_to_pto ddecls h2)
    | IH.PtoNode _ | IH.HTrue | IH.HFalse | IH.HEmp | IH.PredNode _ -> h
  in helper h0

let convert_heap2_x ddecls (f0 : IF.t) : IF.t =
  let rec helper f = match f with
    | IF.Or (f1, f2, pos) ->
          let tmp1 = helper f1 in
          let tmp2 = helper f2 in
          IF.Or (tmp1, tmp2, pos)
    | IF.Base fb ->
          let h = h_convert_heap2 ddecls fb.ISH.base_heap in
          IF.Base { fb with ISH.base_heap = h; }
    | IF.Exists (fb, quans) ->
          let h = h_convert_heap2 ddecls fb.ISH.base_heap in
          IF.Exists ({fb with ISH.base_heap = h}, quans)
  in helper f0

let convert_heap2 ddecls (f0: IF.t) : IF.t =
  let pr = IF.string_of in
  Debug.no_1 "convert_heap2" pr pr (convert_heap2_x ddecls) f0

let float_out_exps_from_heap_x  (f: IF.t ) : IF.t =
  let rec float_ann_var (l, c)=
    match c with
      | IE.Var _ -> (c,[])
      | IE.Ann_Exp (e ,_,_) -> float_ann_var (l, e)
      (* | IE.Null l -> (IE.Var ((null_name, Unprimed) ,l), []) *)
      | _ ->
            let nn = ((fresh_any_name "flted"),Unprimed) in
            let nv = IE.Var (nn,l) in
            let npf = IP.BForm (Iterm.mkEq nv c l) in
            (nv,[(nn,npf)])
  in
  let rec float_out_exps (f: IH.t):(IH.t * (((ident*primed)*IP.t)list)) =
    match f with
      | IH.Star (h1, h2, pos)->
            let r11,r12 = float_out_exps h1 in
            let r21,r22 = float_out_exps h2 in
            (IH.Star (r11, r21, pos), (r12@r22))
      | IH.PredNode b->
            let na,ls = List.split (List.map float_ann_var (List.map (fun v -> b.IHN.hpred_pos,v) b.IHN.hpred_arguments)) in
            (IH.PredNode ({b with IHN.hpred_arguments = na}),(List.concat ls))
      | IH.PtoNode b ->
            let na,ls = List.split (List.map float_ann_var (List.map (fun v -> b.IHN.heap_pos,v) b.IHN.heap_arguments)) in
            (IH.PtoNode ({b with IHN.heap_arguments = na}),(List.concat ls))
      | IH.HeapNode2 b ->
            let prep_one_arg_helper (id,c) =
              let nn = ((fresh_any_name "flted"),Unprimed) in
              let nv = IE.Var (nn,b.IHN.heap2_pos) in
              let npf = IP.BForm (Iterm.mkEq nv c b.IHN.heap2_pos) in
              ((id,nv),[(nn,npf)]) in
            let rec helper (id, c)=
              match c with
                | Iexp.Var _ -> ((id,c),[])
                | Iexp.Ann_Exp (e ,_,_) -> helper (id, e)
                | _ -> prep_one_arg_helper (id,c)
            in
            let na,ls = List.split (List.map helper b.IHN.heap2_arguments) in
            (IH.HeapNode2 ({b with IHN.heap2_arguments = na;}),(List.concat ls))
      | IH.HTrue -> (f,[])
      | IH.HFalse -> (f,[])
      | IH.HEmp  -> (f,[])
  in

  let float_out_exps (f: IH.t):(IH.t * (((ident*primed)*IP.t)list)) =
    let pr1 = IH.string_of in
    let pr2 = pr_pair pr1 (pr_list (pr_pair (fun (i,_) -> i) IP.string_of)) in
    Debug.no_1 "float_out_exps" pr1 pr2 float_out_exps f in

  let rec helper (f:IF.t):IF.t =
    match f with
    | IF.Base b ->
          let rh,rl = float_out_exps b.ISH.base_heap in
          if (List.length rl) == 0 then
            IF.Base { b with ISH.base_heap = rh; }
          else
            let r1,r2 = List.hd rl in
            let r1,r2 = List.fold_left (fun (a1,a2) (c1,c2) ->
                ((c1::a1),(IP.mkAnd a2 c2 b.ISH.base_pos))) ([r1],r2) (List.tl rl) in
            IF.mkExists r1 rh (IP.mkAnd r2 b.ISH.base_pure b.ISH.base_pos) b.ISH.base_pos
    | IF.Exists (b, quans) ->
          let rh,rl = float_out_exps b.ISH.base_heap in
          if (List.length rl)== 0 then
            IF.Exists ({ b with ISH.base_heap = rh; }, quans)
          else
            let r1,r2 = List.hd rl in
            let r1,r2 = List.fold_left (fun (a1,a2) (c1,c2) ->
                ((c1::a1),(IP.mkAnd a2 c2 b.ISH.base_pos))) ([r1],r2) (List.tl rl) in
            IF.mkExists (r1@quans) rh (IP.mkAnd r2 b.ISH.base_pure b.ISH.base_pos) b.ISH.base_pos
    | IF.Or (f1, f2, pos) -> IF.Or (helper f1, helper f2, pos)
  in helper f

let float_out_exps_from_heap (f: IF.t ) : IF.t =
  let pr = IF.string_of in
  Debug.no_1 "float_out_exps_from_heap" pr pr (fun _ -> float_out_exps_from_heap_x  f) f

let normalize_formula_x ddecls (f: IF.t): IF.t =
  let f = convert_heap2 ddecls f in
  let f = float_out_exps_from_heap f in
  (* let f = float_out_min_max f in *)
  let f = IF.rename_bound_vars f in
  f

let normalize_formula ddecls (f: IF.t): IF.t =
  let pr = IF.string_of in
  Debug.no_1 "normalize_formula" pr pr (fun _ -> normalize_formula_x ddecls f) f
