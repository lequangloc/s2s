open Globals
open Gen.Basic
open VarGen

module IHN = IheapNode

type formula =
  | Star of (formula * formula * loc)
  | PtoNode of IheapNode.pto
  | HeapNode2 of IheapNode.heap2
  | PredNode of IheapNode.hpred
  | HEmp
  | HTrue
  | HFalse

and t = formula

let string_of h0=
  let rec helper h= match h with
    | Star (h1, h2, _) -> (helper h1) ^ " * " ^ (helper h2)
    | PtoNode n -> IheapNode.string_of_pto n
    | HeapNode2 n -> IheapNode.string_of_heap2 n
    | PredNode n -> IheapNode.string_of_hpred n
    | HEmp -> "emp"
    | HTrue -> "htrue"
    | HFalse -> "hfalse"
  in
  helper h0

let mkHTrue p = HTrue

let mkHFalse p = HFalse

let mkPtoNode c id deref dr hl l=
  PtoNode (IheapNode.mkPtoNode c id deref dr hl l)

let mkHeapNode2 c id deref dr hl l=
  HeapNode2 (IheapNode.mkNode2 c id deref dr hl l)

let mkPredNode id deref dr hl l=
  PredNode (IheapNode.mkPredNode id deref dr hl l)

let mkStar h1 h2 l=
  Star (h1, h2, l)

let h_apply_one ((fr, t) as s : ((ident*primed) * (ident*primed))) (f0 : t) =
  let rec helper f = match f with
    | Star (f1, f2, pos) ->
          Star (helper f1, helper f2, pos)
    | PtoNode ({IHN.heap_node = x;
      IHN.heap_name = c;
      IHN.heap_deref = deref;
      IHN.heap_derv = dr;
      IHN.heap_arguments = args;
      IHN.heap_pos = pos}) ->
          PtoNode ({IHN.heap_node = Iexp.v_apply_one s x;
          IHN.heap_name = c;
          IHN.heap_deref = deref;
          IHN.heap_derv = dr;
          IHN.heap_arguments = List.map (Iexp.e_apply_one s) args;
          IHN.heap_pos = pos})
    | PredNode p -> PredNode { p with
          IHN.hpred_arguments = List.map (Iexp.e_apply_one s)
              p.IHN.hpred_arguments;
      }
    | HeapNode2 ({ IHN.heap2_node = x;
      IHN.heap2_name = c;
      IHN.heap2_deref = deref;
      IHN.heap2_derv = dr;
      IHN.heap2_arguments = args;
      IHN.heap2_pos= pos}) ->
          HeapNode2 ({ IHN.heap2_node = Iexp.v_apply_one s x;
          IHN.heap2_name = c;
          IHN.heap2_deref = deref;
          IHN.heap2_derv = dr;
          IHN.heap2_arguments = List.map (fun (c1,c2)-> (c1,(Iexp.e_apply_one s c2))) args;
          IHN.heap2_pos = pos})
    | HTrue -> f
    | HFalse -> f
    | HEmp  -> f
  in helper f0

let get_anon_var h0=
  let contain_anon (id, _) =
    if String.length id < 4 then false else
      let subs = String.sub id 0 4 in
      String.compare subs VarGen.qvar_id == 0
  in
  let rec aux h res= match h with
    | PtoNode ({IHN.heap_node = x;
      IHN.heap_arguments = args;}) ->
          let vars = List.fold_left (fun acc e -> acc@(Iexp.fv e)) [] args in
          res@(List.filter contain_anon ([x]@vars))
    | HeapNode2 ({ IHN.heap2_node = x;
      IHN.heap2_name = c;
      IHN.heap2_arguments = args;}) ->
          let vars = List.fold_left (fun acc (_, e) -> acc@(Iexp.fv e)) [] args in
          res@(List.filter contain_anon ([x]@vars))
    | PredNode {IHN.hpred_arguments = args}  ->
          let vars = List.fold_left (fun acc e -> acc@(Iexp.fv e)) [] args in
          res@(List.filter contain_anon vars)
    | Star (h1, h2, _) ->
          let res1 = aux h1 res in
          aux h2 res1
    | HTrue | HFalse | HEmp -> res
  in aux h0 []
