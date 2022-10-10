open VarGen


let num_string_var = 1000

let seq_number = ref 10
let trailer_num_list = ref []
let semp = '\t'
let tbl_string_int = Hashtbl.create num_string_var
let tbl_int_string = Hashtbl.create num_string_var



let qvar_id = "Anon"
let mul_eq_words = ref true

(* type *)
type ident = string

type typ =
  | UNK
  | TVar of int
  | Bool
  | Float
  | Int
  | String
  | Tup2 of typ * typ
  | NUM
  | Void
  | List of typ
  | BagT of typ
  | Named of ident (* named type, could be enumerated or object *)
  (* Named "R" *)
  | Array of (typ * int) (* base type and dimension *)
  | RelT of (typ list) (* relation type *)
  | HpT (* heap predicate relation type *)
  | Pointer of typ (* base type and dimension *)

type rec_kind=
  | NOREC
  | SELFREC
  | MUTREC of string list

let string_of_rec_kind r=
  match r with
    | NOREC -> "norec"
    | SELFREC -> "selfrec"
    | MUTREC k -> "mutrc " ^ (String.concat ";" k)

let void_type = Void

let int_type = Int

let float_type = Float

let bool_type = Bool

let char_type = String

let string_type = String

let bool_type = Bool

let bag_type = BagT Int

let res_name = "res"
let null_name = "_null"
let this = "this"
let self = "self"
let null_type = Named ""
let generic_pointer_type_name = "_GENERIC_POINTER_"

let b_pointer_arith = ref true

let is_null name =
  name == null_name

let is_null_type t  =
  t == null_type

let is_RelT x =
  match x with
  | RelT _ -> true
  | _ -> false

let is_undef_typ t =
  match t with
  | UNK | RelT _ -> true
  | _ -> false

let is_ptr_arith t =
  match t with
  | Named _ -> true
  | Array _ -> true
  | _ -> false

let is_node_typ t =
  match t with
  | Named _ -> true
  | _ -> false

let is_possible_node_typ t =
  match t with
  | Named _ | TVar _  | UNK -> true
  | _ -> false

let char_2_int c=
  match c with
    | 'a' -> 1
    | 'b' -> 2
    | 'c' -> 3
    | 'd' -> 4
    | _ -> failwith "globals.char_2_in"

let int_2_char c=
  match c with
    | 1 -> 'a'
    | 2 -> 'b'
    | 3 -> 'c'
    | 4 -> 'd'
    | _ -> failwith "globals.char_2_in"

type typed_ident = (typ * ident)

exception Illegal_Prover_Format of string
exception NOT_HANDLE_YET


let illegal_format s = raise (Illegal_Prover_Format s)

let string_cmp s1 s2 = String.compare s1 s2

let string_eq s1 s2 = (string_cmp s1 s2) = 0

let pr_lst s f xs = String.concat s (List.map f xs)

let pr_list_brk open_b close_b f xs  = open_b ^(pr_lst ";" f xs)^close_b
let pr_list f xs = pr_list_brk "[" "]" f xs
let pr_list_angle f xs = pr_list_brk "<" ">" f xs
let pr_list_round f xs = pr_list_brk "(" ")" f xs

let pr_pair f1 f2 (x,y) = "("^(f1 x)^","^(f2 y)^")"

(* pretty printing for types *)
let rec string_of_typ (x:typ) : string = match x with
  | UNK          -> "Unknown"
  | Bool          -> "boolean"
  | Float         -> "float"
  | Int           -> "Int"
  | Void          -> "void"
  | NUM          -> "NUM"
  | Tup2 (t1,t2)  -> "tup2("^(string_of_typ t1) ^ "," ^(string_of_typ t2) ^")"
  | BagT t        -> "bag("^(string_of_typ t)^")"
  | TVar t        -> "TVar["^(string_of_int t)^"]"
  | List t        -> "list("^(string_of_typ t)^")"
  | RelT a      -> "RelT("^(pr_list string_of_typ a)^")"
  | HpT        -> "HpT"
  | String -> "String"
  | Named ot -> if ((String.compare ot "") ==0) then "null_type" else ot
  | Pointer t        -> "Pointer{"^(string_of_typ t)^"}"
  | Array (et, r) ->
        let rec repeat k = if (k <= 0) then "" else "[]" ^ (repeat (k-1)) in
        (string_of_typ et) ^ (repeat r)
;;

let subs_tvar_in_typ t (i:int) nt =
  let rec helper t = match t with
    | TVar j -> if i==j then nt else t
    | BagT et -> BagT (helper et)
    | List et -> List (helper et)
    | Array (et,d) -> Array (helper et,d)
    | _ -> t
  in helper t
;;

let string_of_pos p = string_of_int p

let source_files = ref ([] : string list)

let time_out = 3
let solver_timeout_limit = ref 0.
let time_limit_large = ref 0.5
let enable_count_stats = ref true

let web_compile_flag = ref false


(* get counter example *)
let get_model = ref false

let z3_proof_log_list = ref ([]: string list)
let z3_time = ref 0.0

let proof_logging_txt = ref false
let add_to_z3_proof_log_list (f: string) =
  z3_proof_log_list := !z3_proof_log_list @ [f]

let print_original_solver_output = ref false
let print_original_solver_input = ref false



(*
0: smt2
1: core (sl)
*)
let fe = ref (1: int)
let smt_horn = ref (false : bool)

let to_smt2 = ref (false: bool)
let to_smt2_trau = ref (false: bool)

let seq_number = ref (0: int)

let fresh_int () =
  seq_number := !seq_number + 1;
  !seq_number

let show_push_list = ref (None:string option)
let show_push_list_rgx = ref (None:Str.regexp option)

let proof_no = ref 0

let next_proof_no () =
  proof_no := !proof_no + 1;
  !proof_no

let get_proof_no () = !proof_no

let get_proof_no_str () = string_of_int !proof_no

let solver_proof_no = ref 0

let last_solver_fail_no = ref 0

let get_solver_no () = !solver_proof_no

let set_solver_no n = solver_proof_no:=n

let get_last_solver_fail () = !last_solver_fail_no

let set_last_solver_fail () = 
  last_solver_fail_no := !solver_proof_no


let idf (x:'a) : 'a = x

let rec gcd (a: int) (b: int): int = 
  if b == 0 then a
  else gcd b (a mod b)

let gcd_l (l: int list): int =
  let l = List.filter (fun x -> x != 0) l in
  match l with
  | [] -> 1
  | x::[] -> 1
  | x::xs -> List.fold_left (fun a x -> gcd a x) x xs

let lcm (a: int) (b: int): int = (a * b) / (gcd a b)

let lcm_l (l: int list): int =
  if List.exists (fun x -> x == 0) l then 0
  else match l with
    | [] -> 1
    | x::[] -> x
    | x::xs -> List.fold_left (fun a x -> lcm a x) x xs


let fresh_int () =
  let rec find i lst = match lst with
    | [] -> false,[]
    | hd::tl ->
      try
        let hd_int = int_of_string hd in
        if i = hd_int then true,tl
        else if i < hd_int then false,lst
        else find i tl
      with _ -> find i tl
  and helper i =
    let is_mem,trailer_num_list_tail = find i !trailer_num_list in
    let () = trailer_num_list := trailer_num_list_tail in
    if is_mem then helper (i+1) else i
  in
  seq_number := helper (!seq_number + 1);
  !seq_number

let fresh_trailer () =
  let str = string_of_int (fresh_int ()) in
  "_" ^ str

let fresh_any_name (any:string) =
  let str = string_of_int (fresh_int ()) in
  any ^"_"^ str

let fresh_name () =
  let str = string_of_int (fresh_int ()) in
  "f_r_" ^ str

(* map a string variable to its length.
 If not found, create new*)
let lookup_sleng_insert str_sv_id=
   try
     Hashtbl.find tbl_string_int str_sv_id
   with Not_found ->
       let n_id = fresh_any_name str_sv_id in
       let () = Hashtbl.add tbl_string_int str_sv_id n_id in
       let () = Hashtbl.add tbl_int_string n_id str_sv_id in
       n_id

let lookup_sleng str_sv_id=
  Hashtbl.find tbl_string_int str_sv_id

let lookup_svar_from_ivar str_int_id= Hashtbl.find tbl_int_string str_int_id

let fresh_old_name (s: string):string = 
  let slen = (String.length s) in
  let ri = 
    try  
      let n = (String.rindex s '_') in
      let l = (slen-(n+1)) in
      if (l==0) then slen-1
      else 
        n
    with  _ -> slen in
  let n = ((String.sub s 0 ri) ^ (fresh_trailer ())) in
  n


(* *GLOBAL_VAR* substitutions list, used by omega.ml and ocparser.mly
 * moved here from ocparser.mly *)
let omega_subst_lst = ref ([]: (string*string*typ) list)
let dis_provers_timeout = ref false
let user_sat_timeout = ref false
let sat_timeout_limit = ref 5.
let non_linear_flag = ref true
let oc_warning = ref false


(* inv *)
let is_inferring = ref false
let fixcalc_disj = ref 2 (* should be n+1 where n is the base-case *)
let do_under_baga_approx = ref false (* flag to choose under_baga *)
let infer_inv = ref true
let gen_fixcalc = ref true

(*infer*)
let reverify_flag = ref false


let is_substr s id =
  let len_s = String.length s in
  try
    let s_id = String.sub id 0 len_s in
    if (s = s_id) then true
    else false
  with _ -> false
;;

let is_dont_care_var id =
  if is_substr "#" id
  then true
  else false
;;
