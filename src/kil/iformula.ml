
open Globals
open Gen.Basic
open VarGen
open Gen

module ISH = Isymheap
module IP = Ipure
module IH = Iheap

type formula =
  | Base of ISH.formula
  | Exists of (ISH.formula * ((ident * primed) list))
  | Or of (formula * formula * loc)


and t = formula

let string_of cof0 =
  let rec helper cof =match cof with
    | Base f -> ISH.string_of f
    | Exists (f, qvars) ->"(exists " ^ ((pr_list_no_brk string_of_pid) qvars) ^ ": "
            ^ (ISH.string_of f) ^ ")"
    | Or (cof1, cof2, _) -> (helper cof1)^ " \n  or " ^ (helper cof2)
  in helper cof0

let mkTrue p = Base (ISH.mkTrue p)

let mkFalse p = Base (ISH.mkFalse p)

let mkBase h p l =
  Base (ISH.mk h p l)

let isFalse f0=
  let rec aux f=
    match f with
      | Base fb
      | Exists (fb, _) -> (fb.ISH.base_heap == IH.HFalse) || (Ipure.isConstFalse fb.ISH.base_pure)
      | Or (f1, f2, _) -> (aux f1) && (aux f2)
  in aux f0

let mkExists quans h p pos =
   match h with
  | Iheap.HFalse -> mkFalse pos
  | _ ->
        if IP.isConstFalse p then mkFalse pos
        else
          Exists (ISH.mk h p pos, quans)

let mkOr f1 f2 l = Or (f1, f2, l)

let rec apply_one ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : t) =
  match f with
    | Or (f1, f2, pos) -> Or (apply_one s f1, apply_one s f2, pos)
    | Base fb ->
          Base ({ fb with
              ISH.base_heap = IH.h_apply_one s fb.ISH.base_heap;
              ISH.base_pure = IP.apply_one s fb.ISH.base_pure;
          })
  | Exists (fb, qsv) ->
    if List.mem (fst fr) (List.map fst qsv) then f
    else Exists ({ fb with
        ISH.base_heap = IH.h_apply_one s fb.ISH.base_heap;
        ISH.base_pure = IP.apply_one s fb.ISH.base_pure;}, qsv)

let rec subst sst (f : t) = match sst with
  | s :: rest -> subst rest (apply_one s f)
  | [] -> f

let rec rename_bound_vars_x (f : t) =
  match f with
    | Or (f1, f2, pos)-> mkOr (rename_bound_vars_x f1) (rename_bound_vars_x f2) pos
    | Base _ -> f
    | Exists (base_f, qvars) ->
          let new_qvars = Iexp.fresh_vars qvars in
          let rho = List.combine qvars new_qvars in
          let new_base_f = ISH.subst rho base_f in
          Exists (new_base_f, new_qvars)

and rename_bound_vars (f : t): t =
  let pr = string_of in
  Debug.no_1 "ISH.rename_bound_vars" pr pr rename_bound_vars_x f

let is_empty_heap f0=
  let rec aux f = match f with
    | Base fb -> fb.ISH.base_heap == IH.HEmp
    | Exists (fb, _)  -> fb.ISH.base_heap == IH.HEmp
    | Or (f1, f2, _) -> (aux f1) && (aux f2)
  in aux f0
