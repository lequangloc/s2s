open Globals
open Gen
open VarGen

(* spec var *)
type var = {
    t : typ ;
    id:  ident;
    p: primed;
}


type t = var

type pair = t * t

let null_var = {t = null_type ;
    id = null_name;
    p = Unprimed;
}

(* *GLOBAL_VAR* substitutions list, used by omega.ml and ocparser.mly *)
(* let omega_subst_lst = ref ([]: (string * string * typ) list) *)


let mk ty vn pr = {
  t=ty;
  id = vn;
  p = pr }


let mk_unprimed t id = mk t id Unprimed


let compare sv1 sv2=
  let r = string_cmp sv1.id sv2.id in
  if (* (sv1.t = sv2.t) && *)
   r ==0 then if (sv1.p=sv2.p) then 0 else -1
  else r

let equal sv1 sv2 = (* (compare sv1 sv2) == 0 *)
  if string_cmp sv1.id sv2.id == 0 then (sv1.p=sv2.p)
  else false

let equal_pair_vars (sv1, sv2) (sv3, sv4) =
  (equal sv1 sv3 && equal sv2 sv4) ||
      (equal sv1 sv4 && equal sv2 sv3)

let string_of sv =
  let isv = try
    let sv = Globals.lookup_svar_from_ivar sv.id in
    "|" ^ sv ^"|"
  with Not_found ->( sv.id)
  in
  if !print_type then "(" ^ isv ^(":" ^ string_of_typ sv.t) ^ ")" else isv

let string_of_pair = pr_pair string_of string_of

let string_of_full sv =
  ("(" ^ sv.id ^ (string_of_primed sv.p) ^ ":" ^ string_of_typ sv.t ^ ")")

let string_of_type sv =
  ("(" ^ sv.id ^ ":" ^ string_of_typ sv.t ^ ")")

let string_of_list xs =
   "["^(String.concat "," (List.map (string_of) xs))^"]"

let string_of_full_list xs =
   "["^(String.concat "," (List.map (string_of_full) xs))^"]"


let name_of v = v.id

let type_of v = v.t

let is_primed v = v.p == Primed

let is_rel_typ sv = match sv.t with
  | RelT _ -> true
  | _ -> false

let is_node sv = is_node_typ sv.t

let is_arr_typ sv = match sv.t with
  | Array _ -> true
  | _ -> false

let is_inter_deference_spec_var sv =
  let re = Str.regexp "^deref_f_r_" in
  Str.string_match re sv.id 0

let remove_dups vl = Gen.BList.remove_dups_eq equal vl

let mem (sv : t) (svs : t list) : bool =
  List.exists (fun v -> equal sv v) svs

let intersect svs1 svs2 = Gen.BList.intersect_eq equal
  svs1 svs2

let diff svs1 svs2 = Gen.BList.difference_eq equal
  svs1 svs2

(* let eq_closure sst0 vars0= *)
(*   let rec aux_loop (v1, v2) ls new_vars= *)
(*     match ls with *)
(*       | v3::rest -> begin *)
(*           let new_vars1 = if equal v3 v1 then *)
(*             new_vars@[v2] *)
(*           else if equal v3 v2 then *)
(*             new_vars@[v1] *)
(*           else new_vars *)
(*           in aux_loop (v1, v2) rest new_vars1 *)
(*         end *)
(*       | [] -> new_vars *)
(*   in *)
(*   let rec sst_loop sst vars res= *)
(*     match sst with *)
(*       | hd::tl -> let n_vars = aux_loop hd vars [] in *)
(*         sst_loop tl vars (res@n_vars) *)
(*       | [] -> res *)
(*   in *)
(*   let rec fixpoint sst vars= *)
(*     let n_vars = sst_loop sst vars [] in *)
(*     let incr_vars = diff n_vars vars in *)
(*     if incr_vars == [] then vars else *)
(*       fixpoint sst (vars@incr_vars) *)
(*   in *)
(*   fixpoint sst0 vars0 *)

let get_eq_closure sst vars0=
  let rec aux vars res=
    let new_vars = List.fold_left (fun acc (v1, v2) ->
        let b1 = mem v1 res in
        let b2 = mem v2 res in
        match b1, b2 with
          | false, false
          | true, true -> acc
          | true, false -> acc@[v2]
          | false, true -> acc@[v1]
    ) vars sst in
    let d = diff new_vars res in
    if d == [] then res
    else aux d (res@d)
  in if sst==[] then vars0 else aux vars0 vars0

let fresh_var (sv : var) =
  let old_name = name_of sv in
  let name = fresh_old_name old_name in
  let t = type_of sv in
  mk t name Unprimed (* fresh names are unprimed *)

let fresh_vars (svs : t list) = List.map fresh_var svs

let subst sst sv=
  try List.assoc sv sst
  with Not_found -> sv

let subst_var_par (sst:(t * t) list) (o : t) : t =
  let rec helper sst o= match sst with
    | [] -> o
    | (v1,v2)::tail -> helper tail (if equal o v1 then v2 else o) in
  helper sst o

let lookup_length_var_of_string sv =
  let isv_id = Globals.lookup_sleng_insert sv.id in
  {t = Int; id = isv_id;
  p = sv.p;
  }


let null_var = mk Globals.null_type Globals.null_name Unprimed

let subst_type t_sst sv=
  let _, n_t = List.find (fun (t1, _) -> t1 = sv.t) t_sst in
  {sv with t = n_t}

let to_parallel_subst_x sst=
  let rec aux grps eqs=
    match eqs with
      | (v1, v2)::rest -> begin
          let inter, rem = List.partition (fun ls ->
              mem v1 ls || mem v2 ls
          ) grps in
          let n_grps=
            if inter == [] then rem@[[v1;v2]] else
              let n_grp = remove_dups ((List.concat inter)@[v1;v2]) in
              rem@[n_grp]
          in aux n_grps rest
        end
      | [] -> grps
  in
  if sst == [] then []
  else
    let grps = aux [] sst in
    List.fold_left (fun r ls->
        match ls with
          | x::rest -> let new_sst = List.map (fun v1 -> (v1, x)) rest in
            r@new_sst
          | [] -> r
    ) [] grps

let to_parallel_subst sst=
  let pr1 = pr_list string_of_pair in
  Debug.no_1 "to_parallel_subst" pr1 pr1
      (fun _ -> to_parallel_subst_x sst) sst
