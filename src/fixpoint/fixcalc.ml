open Globals
open Ustr
open VarGen
open Gen.Basic

module DD = Debug

module CF = Cformula
module CB = Csymheap
module CP = Cpure
module CH = Cheap
module CPeN = CpredNode
module CPoN = CptoNode

(* Operators *)
let op_lt = "<"
let op_lte = "<="
let op_gt = ">"
let op_gte = ">="
let op_eq = "="
let op_neq = "!="
let op_and = " && "
let op_or = " || "
let op_add = "+"
let op_sub = "-"


(*
let fixcalc_exe = if !VarGen.is_solver_local then (ref "./fixcalc ") else (ref "fixcalc ")
*)

let fixcalc_options = " -v:-1"

(* to suppress some printing *)

let syscall cmd =
  let () = Debug.ninfo_hprint (add_str  "cmd" pr_id) cmd no_pos in
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  let todo_unk = Unix.close_process (ic, oc) in
  (Buffer.contents buf)

let rec remove_paren s n = if n=0 then "" else match s.[0] with
    | '(' -> remove_paren (String.sub s 1 (n-1)) (n-1)
    | ')' -> remove_paren (String.sub s 1 (n-1)) (n-1)
    | _ -> (String.sub s 0 1) ^ (remove_paren (String.sub s 1 (n-1)) (n-1))


let gen_fixcalc_file str_fc=
  let file_name = (fresh_any_name "logs/gen_fixc") ^ ".fc" in
  let out_chn =
    let reg = Str.regexp "\(\.ss\)\|\(.slk\)" in
    let () = Debug.ninfo_hprint (add_str "generating fixcalc file" pr_id) file_name no_pos in
    (try Unix.mkdir "logs" 0o750 with _ -> ());
    (*open_out*) open_out_gen [Open_wronly; Open_append; Open_creat] 0o600 (file_name)
  in
  let () = output_string out_chn str_fc in
  let () = close_out out_chn in
  ()

let rec string_of_elems elems string_of sep = match elems with
  | [] -> ""
  | h::[] -> string_of h
  | h::t -> (string_of h) ^ sep ^ (string_of_elems t string_of sep)


let fixcalc_of_var x = match x.Var.p with
  | Unprimed -> x.Var.id
  | Primed -> "PRI" ^ x.Var.id

let fixcalc_of_var x =
  DD.no_1 "fixcalc_of_var" Var.string_of (fun c->c) fixcalc_of_var x

let rec fixcalc_of_exp_list e op number = match number with
  | 0 -> ""
  | 1 -> fixcalc_of_exp e
  | n -> fixcalc_of_exp e ^ op ^ (fixcalc_of_exp_list e op (n-1))

and fixcalc_of_exp e = match e with
  | Exp.Null _ -> "null"
  | Exp.Var (x, _) -> fixcalc_of_var x
  | Exp.IConst (i, _) -> string_of_int i
  | Exp.FConst (f, _) -> string_of_float f
  | Exp.Add (e1, e2, _) -> fixcalc_of_exp e1 ^ op_add ^ fixcalc_of_exp e2
  | Exp.Subtract (e1, e2, _) ->
    fixcalc_of_exp e1 ^ op_sub ^ "(" ^ fixcalc_of_exp e2 ^ ")"
  | Exp.Mult (e1, e2, _) ->
    begin
      match e1, e2 with
      | (Exp.IConst (i,_), Exp.IConst (j,_)) -> string_of_int (i*j)
      | (Exp.IConst (i,_),_) ->
            if i >= 0 then
              fixcalc_of_exp_list e2 op_add i
            else
              "0 " ^ op_sub ^ (fixcalc_of_exp_list e2 op_sub (-i))
      | (_,Exp.IConst (i,_)) ->
            if i >= 0 then
              fixcalc_of_exp_list e1 op_add i
            else
              "0 " ^ op_sub ^ (fixcalc_of_exp_list e1 op_sub (-i))
      | _ -> illegal_format ("Fixcalc.fixcalc_of_exp: Not supported expression")
    end
  | _ ->
        let () = Debug.tinfo_hprint (add_str "fixcalc_of_exp error :" (fun _ -> "" )) e no_pos in
        illegal_format ("Fixcalc.fixcalc_of_exp: Not supported expression")

let fixcalc_of_exp f=
  DD.no_1 "fixcalc_of_exp" Exp.string_of (fun s->s) (fun f-> fixcalc_of_exp f) f
;;

let fixcalc_of_bool b =
  match b with
  | true -> "1=1"
  | false -> "1=0"

let rec fixcalc_of_term pf =
  match pf with
  | Term.BConst (b,_) -> fixcalc_of_bool b
  | Term.BVar (x, _) -> fixcalc_of_var x
  | Term.Lt (e1, e2, _) -> fixcalc_of_exp e1 ^ op_lt ^ fixcalc_of_exp e2
  | Term.Lte (e1, e2, _) -> fixcalc_of_exp e1 ^ op_lte ^ fixcalc_of_exp e2
  | Term.Gt (e1, e2, _) -> fixcalc_of_exp e1 ^ op_gt ^ fixcalc_of_exp e2
  | Term.Gte (e1, e2, _) -> fixcalc_of_exp e1 ^ op_gte ^ fixcalc_of_exp e2
  | Term.Eq (e1, e2, _) ->
        if Exp.is_null e2 then fixcalc_of_exp e1 ^ op_lte ^ "0"
        else
          if Exp.is_null e1 then fixcalc_of_exp e2 ^ op_lte ^ "0"
          else fixcalc_of_exp e1 ^ op_eq ^ fixcalc_of_exp e2
  | Term.Neq (e1, e2, _) ->
        if Exp.is_null e1 then
          let s = fixcalc_of_exp e2 in s ^ op_gt ^ "0"
        else
          if Exp.is_null e2 then
            let s = fixcalc_of_exp e1 in s ^ op_gt ^ "0"
          else
            let s = fixcalc_of_exp e1 in
            let t = fixcalc_of_exp e2 in
            "((" ^ s ^ op_lt ^ t ^ ")" ^ op_or ^ "(" ^ s ^ op_gt ^ t ^ "))"
  | Term.EqMax (e1, e2, e3, _) ->
        let e1str = fixcalc_of_exp e1 in
        let e2str = fixcalc_of_exp e2 in
        let e3str = fixcalc_of_exp e3 in
        "((" ^ e2str ^ " >= " ^ e3str ^ " && " ^ e1str ^ " = " ^ e2str ^ ") || ("
        ^ e3str ^ " > " ^ e2str ^ " && " ^ e1str ^ " = " ^ e3str ^ "))"
  | Term.EqMin (e1, e2, e3, _) ->
        let e1str = fixcalc_of_exp e1 in
        let e2str = fixcalc_of_exp e2 in
        let e3str = fixcalc_of_exp e3 in
        "((" ^ e2str ^ " <= " ^ e3str ^ " && " ^ e1str ^ " = " ^ e2str ^ ") || ("
        ^ e3str ^ " < " ^ e2str ^ " && " ^ e1str ^ " = " ^ e3str ^ "))"
  | Term.RelForm (id,args,_) ->
        let () = Debug.ninfo_hprint (add_str "fixcalc_of_term RelForm: " Term.string_of) pf no_pos in
        if List.exists
          (fun x -> match x with
            | Exp.IConst _ -> true
            | _ -> false) args
        then "0=0"
        else
          ((* fixcalc_of_var *) id) ^ "(" ^
              (string_of_elems args fixcalc_of_exp ",") ^ ")"
  | _ ->
    let () = Debug.ninfo_hprint (add_str "fixcalc trans error :" Term.string_of) pf no_pos in
    illegal_format ("Fixcalc.fixcalc_of_term: Do not support bag, list")

let fixcalc_of_term f=
  DD.no_1 "fixcalc_of_term" Term.string_of (fun s->s) (fun f-> fixcalc_of_term f) f
;;

let rec fixcalc_of_pure_formula f = match f with
  | CP.BForm (Term.BVar (x,_)) -> fixcalc_of_var x ^ op_gt ^ "0"
  | CP.BForm b -> fixcalc_of_term b
  | CP.And (p1, p2) ->
        "" ^ fixcalc_of_pure_formula p1 ^ op_and ^ fixcalc_of_pure_formula p2 ^ ""
  | CP.Or (p1, p2) ->
        "(" ^ fixcalc_of_pure_formula p1 ^ op_or ^ fixcalc_of_pure_formula p2 ^ ")"
  | CP.Not (p) -> begin
      match p with
        | CP.BForm (Term.BVar (x,_)) -> fixcalc_of_var x ^ op_lte ^ "0"
        | CP.BForm (Term.Eq (e1,e2,loc)) ->
              let new_f = CP.BForm (Term.Neq (e1,e2,loc)) in
              fixcalc_of_pure_formula new_f
        | CP.BForm (Term.Neq (e1,e2,loc)) ->
              let new_f = CP.BForm (Term.Eq (e1,e2,loc)) in
              fixcalc_of_pure_formula new_f
        | _ -> illegal_format ("Fixcalc.fixcalc_of_pure_formula: Not supported Not-formula ::"^(CP.string_of f))
    end
  | CP.Forall (sv, p) ->
        " (forall (" ^ fixcalc_of_var sv ^ ":" ^
            fixcalc_of_pure_formula p ^ ")) "
  | CP.Exists (sv, p) ->
        " (exists (" ^ fixcalc_of_var sv ^ ":" ^
            fixcalc_of_pure_formula p ^ ")) "

let fixcalc_of_pure_formula f=
  DD.no_1 "fixcalc_of_pure_formula" CP.string_of (fun s->s) (fun f-> fixcalc_of_pure_formula f) f
;;


let rec fixcalc_of_h_formula f = match f with
  | CH.Star (h1, h2, _) ->
        "(" ^ fixcalc_of_h_formula h1 ^ op_and ^ fixcalc_of_h_formula h2 ^ ")"
  | CH.PtoNode {CPoN.hpto_node = sv; CPoN.hdata_name = c;
              CPoN.hpto_arguments = svs} ->
        (fixcalc_of_var sv)  ^ op_gt ^ "0"
  | CH.PredNode {CPeN.hpred_name = c; CPeN.hpred_arguments = svs} ->
        let str =
          (* try *)
          (*   let (svl1,pf) = Excore.map_num_invs # find c in *)
          (*   let svl2 = svs in *)
          (*   let svl2 = if (List.length svl1 < List.length svl2) then *)
          (*     List.rev (List.tl (List.rev svl2)) (\* svl2 has idx variable, remove it *\) *)
          (*   else svl2 in *)
          (*   let new_pf = CP.subst (List.combine svl1 svl2) pf in *)
          (*   fixcalc_of_pure_formula new_pf *)
          (* with _ -> *)
              c ^ "(" ^ (string_of_elems svs fixcalc_of_var ",") ^ ")"
      in str
  | CH.HTrue -> "HTrue"
  | CH.HFalse -> "HFalse"
  | CH.HEmp -> "0=0"

let rec fixcalc_of_formula e = match e with
  | CF.Or _ ->
        illegal_format ("Fixcalc.fixcalc_of_formula: Not supported Or-formula")
  | CF.Base {CB.base_heap = h; CB.base_pure = p} ->
        "(" ^ fixcalc_of_h_formula h ^ op_and ^ fixcalc_of_pure_formula p ^ ")"
  | CF.Exists (fb, svs) ->
        " exists (" ^ (string_of_elems svs fixcalc_of_var ",") ^ ": " ^
            fixcalc_of_h_formula fb.CB.base_heap ^ op_and ^ fixcalc_of_pure_formula fb.CB.base_pure ^ ")"

let fixcalc_of_formula e =
  Debug.no_1 "fixcalc_of_formula" CF.string_of pr_id fixcalc_of_formula e


let sl2fix_body lower_invs (fml0: CF.t) vname para_names=
  (*rename to avoid clashing, capture rev_subst also*)
  let vars =  para_names in
  let fr_vars = Var.fresh_vars vars in
  let sst = List.combine vars fr_vars in
  let rev_sst = List.combine fr_vars vars in
  let fs = List.map (fun f ->
      CF.subst sst (CF.subst_view_inv lower_invs f)) (CF.list_of_disjuncts fml0) in
  let input_fixcalc =
    try
      vname ^ ":={[" ^ (string_of_elems fr_vars fixcalc_of_var ",") ^
      "] -> [] -> []: " ^
      (string_of_elems fs (fun c-> fixcalc_of_formula c) op_or) ^
      "\n};\n"
    with _ -> report_error no_pos "slk2fix_body: Error in translating the input for fixcalc"
  in
  DD.ninfo_zprint (lazy (("Input of fixcalc: " ^ input_fixcalc))) no_pos;
  (input_fixcalc, fr_vars, rev_sst)


let sl2fix_header disj_num vnames=
  let () = DD.ninfo_hprint (add_str "vnames" (pr_list pr_id)) vnames no_pos in
  let ls_vnames = String.concat "," vnames in
  let ls_disj_nums=  String.concat "," (List.map (fun _ -> string_of_int disj_num) vnames) in
  let () = DD.ninfo_hprint (add_str "ls_vnames" pr_id) ls_vnames no_pos in
  "bottomupgen([" ^ ls_vnames ^ "], [" ^ ls_disj_nums ^ "], SimHeur);"


(* invoke Fixcalc *)
let compute_invs input_fixcalc=
  let rec get_lines s curp res=
    try
      let n = String.index_from s curp '\n' in
      let str = String.sub s curp (n-curp) in
      if String.length str > 0 then  get_lines s (n+1) res@[str] else res
    with _ ->
      (res)
  in
  let output_of_sl =  "logs/fixcalc"^".inp" in
  let () = DD.ninfo_pprint ("fixcalc file name: " ^ output_of_sl) no_pos in
  let oc = open_out output_of_sl in
  Printf.fprintf oc "%s" input_fixcalc;
  flush oc;
  close_out oc;
  let res =
      syscall (!fixcalc_exe ^" "^ output_of_sl ^ fixcalc_options)
   (* with _ -> Gen.report_error no_pos "fixcalc not found"*)
  in
  (* Remove parentheses *)
  let res = remove_paren res (String.length res) in

  (* Parse result *)
  let () = DD.ninfo_hprint (add_str "res= " pr_id) res no_pos in
  (* let () = print_endline ("res ="^ res) in *)
  let lines = get_lines res 0 [] in
  let () = DD.ninfo_hprint (add_str "lines" (pr_list_ln pr_id)) lines no_pos in
  let invs = List.fold_left (fun r line -> r@(Parse_fix.parse_fix line)) [] lines in
  let () = DD.ninfo_hprint (add_str "res(parsed)= " (pr_list Cpure.string_of)) invs no_pos in
  invs

let compute_invs input_fixcalc =
  let pr = (pr_list CP.string_of) in
  Debug.no_1 "Fixcalc.compute_invs" pr_id pr compute_invs
      input_fixcalc
