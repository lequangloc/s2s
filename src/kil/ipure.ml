
open Globals
open Gen.Basic
open VarGen


type formula =
  | BForm of Iterm.t
  | And of (formula * formula * loc)
  | Or of (formula * formula * loc)
  | Not of (formula * loc)
  | Forall of ((ident * primed) * formula * loc)
  | Exists of (( ident * primed) * formula * loc)

and t = formula

let string_of p0=
  let rec helper p =match p with
    | BForm t -> Iterm.string_of t
    | And (p1, p2, _) -> "(" ^ (helper p1) ^ ") & (" ^ (helper p2)  ^ ")"
    | Or (p1, p2, _) -> "(" ^ (helper p1)  ^ ") | (" ^ (helper p2)  ^ ")"
    | Not (p1, _) -> "!(" ^ (helper p1)  ^ ")"
    | Forall (pid, p1, _) -> "forall " ^ (string_of_pid pid)
                                         ^ ". (" ^ (helper p1) ^ ")"
    | Exists (pid, p1, _) -> "ex " ^ (string_of_pid pid)
                                         ^ ". (" ^ (helper p1) ^ ")"
  in
  helper p0

let mkTrue p = BForm (Iterm.mkTrue p)

let mkFalse p = BForm (Iterm.mkFalse p)

let mkBForm t = BForm t

let mkAnd p1 p2 l = And (p1, p2, l)

let mkOr p1 p2 l = Or (p1, p2, l)

let mkNot p1 l = Not (p1, l)

let isConstTrue p = match p with
  | BForm t -> Iterm.isConstTrue t
  | _ -> false

let isConstFalse p = match p with
  | BForm t -> Iterm.isConstFalse t
  | _ -> false

(* free variables *)
let rec fv (f : formula) : (ident * primed) list = match f with
  | BForm t -> Iterm.fv t
  | And (p1, p2, _) -> combine_pvars p1 p2
  | Or (p1, p2, _) -> combine_pvars p1 p2
  | Not (nf, _) -> fv nf
  | Forall (qid, qf, _) -> remove_qvar qid qf
  | Exists (qid, qf, _) -> remove_qvar qid qf

and combine_pvars p1 p2 =
  let fv1 = fv p1 in
  let fv2 = fv p2 in
  Gen.BList.remove_dups_eq (=) (fv1 @ fv2)

and remove_qvar qid qf =
  let qfv = fv qf in
  Gen.BList.remove_elem_eq (=) qid qfv

let rec mkForall vs f pos = match vs with
  | [] -> f
  | v :: rest ->
        let ef = mkForall rest f pos in
        if List.mem v (fv ef) then
          Forall (v, ef, pos)
        else
          ef

let rec mkExists vs f pos = match vs with
  | [] -> f
  | v :: rest ->
        let ef = mkExists rest f pos in
        if List.mem v (fv ef) then
          Exists (v, ef,  pos)
        else
          ef

let rec apply_one (fr, t) f = match f with
  | BForm bf -> BForm (Iterm.apply_one (fr, t) bf)
  | And (p1, p2, pos) -> And (apply_one (fr, t) p1,
    apply_one (fr, t) p2, pos)
  | Or (p1, p2, pos) -> Or (apply_one (fr, t) p1,
    apply_one (fr, t) p2, pos)
  | Not (p, pos) -> Not (apply_one (fr, t) p,  pos)
  | Forall (v, qf, pos) ->
    if Iexp.eq_var v fr then f
    else if Iexp.eq_var v t then
      let fresh_v = Iexp.fresh_var v in
      Forall (fresh_v, apply_one (fr, t) (apply_one (v, fresh_v) qf),  pos)
    else Forall (v, apply_one (fr, t) qf, pos)
  | Exists (v, qf, pos) ->
    if Iexp.eq_var v fr then f
    else if Iexp.eq_var v t then
      let fresh_v = Iexp.fresh_var v in
      Exists (fresh_v, apply_one (fr, t) (apply_one (v, fresh_v) qf), pos)
    else Exists (v, apply_one (fr, t) qf, pos)

let rec subst sst (f : t) = match sst with
  | s :: rest -> subst rest (apply_one s f)
  | [] -> f
