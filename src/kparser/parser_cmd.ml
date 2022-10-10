
open Camlp4

open Globals
open Gen.Basic
open VarGen
open ParserBasic
open Parser_util
(* open ParserSL *)
open Token
open Icmd
open Inode
open Icfg

module DD = Debug
module IF = Iformula
module IP = Ipure

(* module SLGram = Camlp4.Struct.Grammar.Static.Make(Lexer.Make(Token));; *)

let default_rel_id = "rel_id__"



let sprog = SLGram.Entry.mk "s2prog";;
(* let sprog_int = SLGram.Entry.mk "sprog_int";; *)


EXTEND SLGram
    GLOBAL:sprog;

sprog:[[ t = command_list; `EOF -> t ]];
(* sprog_int:[[ t = command; `EOF -> t ]]; *)

command_list: [[ t = LIST0 non_empty_command_dot -> t ]];

(* command: [[ t=OPT non_empty_command_dot-> un_option t EmptyCmd]]; *)

non_empty_command_dot: [[t=non_empty_command; `DOT -> t]];

non_empty_command:
    [[  t=data_decl           -> DataDecl t
      (* | c=class_decl -> DataDecl c *)
      | t = rel_decl          -> RelDecl t
      | `PRED;t= pred_decl     -> PredDecl t
      | t= checkentail_cmd     -> EntailCheck t
      | t= checksat_cmd     -> SatCheck t
      (* | t= validate_cmd     -> Validate t *)
   ]];

(**************************************)
(* parameter lists *)
(**************************************)
id:[[`IDENTIFIER id-> id]];

id_list:[[t=LIST1 id SEP `COMMA -> t]];


id_type_list_opt: [[ t = LIST0 cid_typ SEP `COMMA -> t ]];

c_typ:
 [[ `COLON; t= typ -> t
 ]];

cid_typ:
  [[ `IDENTIFIER id ; t=OPT c_typ ->
      let ut = un_option t UNK in
      let () =
        if is_RelT ut then
          let () = rel_names # push id in
          ()
        else ()
      in
        (ut,id)
   ]];

gen_args1:
  [[
    `LT; hl= opt_general_h_args; `GT -> hl
  ]];

gen_args_pred:
  [[
    `OPAREN; hl= opt_general_h_args; `CPAREN -> hl
     (* `LT; hl= opt_general_h_args; `GT -> hl *)
  ]];

data_args2:
  [[
    `LT; hl= opt_data_h_args; `GT -> hl
  ]];

opt_general_h_args: [[t = OPT general_h_args -> un_option t ([],[])]];

opt_data_h_args: [[t = OPT data_h_args -> un_option t ([],[])]];

general_h_args:
  [[ t= opt_heap_arg_list2 -> ([],t)
  | t= opt_heap_arg_list -> (t,[])]];

data_h_args:
  [[ t= opt_heap_data_arg_list2 -> ([],t)
  | t= opt_heap_data_arg_list -> (t,[])]];

opt_heap_arg_list: [[t=LIST1 cexp SEP `COMMA -> t]];

opt_heap_arg_list2:[[t=LIST1 heap_arg2 SEP `COMMA -> error_on_dups (fun n1 n2-> (fst n1)==(fst n2)) t (get_pos_camlp4 _loc 1)]];

opt_heap_data_arg_list: [[t=LIST1 cexp_data_p SEP `COMMA -> t]];

opt_heap_data_arg_list2:[[t=LIST1 heap_arg2_data SEP `COMMA -> error_on_dups (fun n1 n2-> (fst n1) == (fst n2)) t (get_pos_camlp4 _loc 1)]];

heap_arg2: [[ peek_heap_args; `IDENTIFIER id ; `EQ;  e=cexp -> (id,e)]]; 

heap_arg2_data: [[ peek_heap_args; `IDENTIFIER id ; `EQ;  e = cexp_data_p -> (id,e)]];

opt_cid_list: [[t=LIST0 cid SEP `COMMA -> error_on_dups (fun n1 n2-> (fst n1)==(fst n2)) t (get_pos_camlp4 _loc 1)]];

cid_list: [[t=LIST1 cid SEP `COMMA -> error_on_dups (fun n1 n2-> (fst n1)==(fst n2)) t (get_pos_camlp4 _loc 1)]];

(** the rules to capture the extension identifiers **)
cid: [[
    `IDENTIFIER t -> if String.contains t '\'' then
      (* Remove the primed in the identifier *)
      (Str.global_replace (Str.regexp "[']") "" t,Primed)
    else (t,Unprimed)
  | `RES _                 	->  (res_name, Unprimed)
  | `SELFT _               	->  (self, Unprimed)
  | `NULL                     ->  (null_name, Unprimed)
  | `THIS _         		->  (this, Unprimed)]];


(* opt_name: [[t= OPT name-> un_option t ""]]; *)

(* name:[[ `STRING(_,id)  -> id]]; *)

typ:
  [[ peek_array_type; t=array_type     ->  t
   | peek_pointer_type; t = pointer_type   -> t
   | t=non_array_type -> t
  ]];

typed_id_list:[[ t = typ; `IDENTIFIER id ->  (t,id) ]];

non_array_type:
  [[ `VOID               -> void_type
   | `INT                -> int_type
   | `FLOAT              -> float_type 
   | `DBL              -> float_type 
   | `BOOL               -> bool_type
   | `BAG               -> bag_type
   | `BAG; `OPAREN; t = non_array_type ; `CPAREN -> BagT t
   | `IDENTIFIER id      -> Named id
   | t=rel_header_view   -> let tl,_ = List.split t.Irel.rel_typed_vars in RelT tl ]];

pointer_type:
  [[ t=non_array_type; r = star_list ->
  let rec create_pointer n =
    if (n<=1) then (Pointer t) else (Pointer (create_pointer (n-1)))
  in
  let pointer_t = create_pointer r in
  pointer_t
   ]];

star_list: [[`STAR; s = OPT SELF -> 1 + (un_option s 0)]];

array_type:
  [[  t=non_array_type; r=rank_specifier -> Array (t, r)]];

rank_specifier:
  [[`OSQUARE; c = OPT comma_list; `CSQUARE -> un_option c 1]];

comma_list: [[`COMMA; s = OPT SELF -> 1 + (un_option s 1)]];

(**************************************)
(* data declaration cmd - data_decl, ( to support class_decl ) *)
(**************************************)
data_decl:
    [[ dh=data_header ; db = data_body
        -> {Inode.data_name = dh;
            Inode.data_pos = get_pos_camlp4 _loc 1;
            Inode.data_fields = db;
            Inode.data_parent_name="Object"; (* Object; *)
            Inode.data_is_template = false;
        } ]];

pure_inv: [[`INV; pf=pure_constr -> pf]];

opt_inv: [[t=OPT pure_inv -> un_option t (IP.mkTrue no_pos)]];

(* opt_pure_inv: [[t=OPT pure_inv -> t ]]; *)

with_typed_var: [[`OSQUARE; typ; `CSQUARE -> ()]];

data_header:
    [[ `DATA; `IDENTIFIER t; OPT with_typed_var ->
        t ]];

data_body:
      [[`OBRACE; fl=field_list2;`SEMICOLON; `CBRACE -> fl
      | `OBRACE; fl=field_list2; `CBRACE   ->  fl
      | `OBRACE; `CBRACE                   -> []] ];

(* field_ann: [[ *)
(*     `HASH;`IDENTIFIER id -> id *)
(*   (\* | `AT;`IDENTIFIER id -> id *\) *)
(* ]]; *)

(* field_anns: [[ *)
(*      anns = LIST0 field_ann -> anns *)
(* ]]; *)

field_list2:[[
    t = typ; `IDENTIFIER n ->
        [((t,n),get_pos_camlp4 _loc 1)]
  (* | t = typ; `IDENTIFIER n ; ann=field_anns -> *)
  (*       [((t,n),get_pos_camlp4 _loc 1,false, ann)] *)
  |  t = typ; `OSQUARE; t2=typ; `CSQUARE; `IDENTIFIER n ->
         [((t,n), get_pos_camlp4 _loc 1)]
  |  t=typ; `IDENTIFIER n; peek_try; `SEMICOLON; fl = SELF ->
         (
	     if List.mem n (List.map Inode.get_field_name fl) then
	       report_error (get_pos_camlp4 _loc 4)
                   (n ^ " is duplicated")
	     else
	       ((t, n), get_pos_camlp4 _loc 3) :: fl
         )
  (* |  t=typ; `IDENTIFIER n; ann=field_anns ; peek_try; `SEMICOLON; fl = SELF -> ( *)
  (*        if List.mem n (List.map Inode.get_field_name fl) then *)
  (*          report_error (get_pos_camlp4 _loc 4) (n ^ " is duplicated") *)
  (*        else *)
  (*          let ann = *)
  (*            if ann=[] then [Inode.gen_field_ann t] else ann *)
  (*          in *)
  (*          ((t, n), get_pos_camlp4 _loc 3, false,ann) :: fl *)
  (*    ) *)
  | t1= typ; `OSQUARE; t2=typ; `CSQUARE; `IDENTIFIER n; peek_try; `SEMICOLON; fl = SELF -> (
        if List.mem n (List.map get_field_name fl) then
	  report_error (get_pos_camlp4 _loc 4) (n ^ " is duplicated")
	else
	  ((t1, n), get_pos_camlp4 _loc 3(* , false, [(gen_field_ann t1)] *)) :: fl
    )
  ]
  ];

(**************************************)
(* rel declaration cmd - rel_decl*)
(**************************************)
rel_decl:[[ rh=rel_header; `EQEQ; rb=rel_body ->
    { rh with Irel.rel_formula = rb; }
  | rh = rel_header -> rh
  | rh = rel_header; `EQ -> report_error (get_pos_camlp4 _loc 2) ("use == to define a relation")
]];

rel_header:[[
`REL; `IDENTIFIER id; `OPAREN; tl= typed_id_list_opt; `CPAREN  ->
    let () = rel_names # push id in
    {
        Irel.rel_name = id;
        Irel.rel_typed_vars = tl;
        Irel.rel_formula = IP.mkTrue (get_pos_camlp4 _loc 1);
    }
]];

rel_header_view:[[
  `REL; `OPAREN; tl= typed_default_id_list_opt; `CPAREN  ->
  let rd = {
      Irel.rel_name = "";
      Irel.rel_typed_vars = tl;
      Irel.rel_formula = IP.mkTrue (get_pos_camlp4 _loc 1);
  } in
  rd
]];


typed_default_id_list:
    [[ t = typ  ->  (t,default_rel_id) ]];

typed_id_list_opt: [[ t = LIST0 typed_id_list SEP `COMMA -> t ]];

typed_default_id_list_opt:
    [[ t = LIST0 typed_default_id_list SEP `COMMA -> t ]];


rel_body:[[ pc=pure_constr -> pc
    (* Only allow pure constraint in relation definition. *)

]];

(**************************************)
(* pred declaration cmd - pred_decl*)
(**************************************)

pred_decl:
  [[ vh= pred_header; `EQEQ; vb=pred_body; oi= opt_inv ->
      { vh with pred_formula = vb;
          Ipred.pred_invariant = oi;
          Ipred.pred_is_prim = false;
          (* pred_kind = Pred_NORM; *)
      }
 ]];

pred_header:
  [[ `IDENTIFIER vn; `LT; l= id_type_list_opt; `GT ->
      let cids_t =  l in
      (* DD.info_hprint (add_str "parser-view_header(cids_t)"
         (pr_list (pr_pair string_of_typ pr_id))) cids_t no_pos; *)
      let _, cids = List.split cids_t in
      let () = pred_names # push vn in
        { Ipred.pred_name = vn;
          Ipred.pred_pos = get_pos_camlp4 _loc 1;
          Ipred.pred_data_name = "";
          Ipred.pred_vars = cids;
          Ipred.pred_parent_name = None;
          Ipred.pred_typed_vars = cids_t;
          Ipred.pred_formula = IF.mkTrue (get_pos_camlp4 _loc 1);
          Ipred.pred_is_prim = false;
          (* pred_kind = Pred_NORM; *)
          Ipred.pred_invariant = IP.mkTrue (get_pos_camlp4 _loc 1);
        }]];

pred_body:
  [[ t = disjunctive_constr -> t
  ]];

(* ann_cid:[[c = cid_typ ->(c)]]; *)
(* opt_cid_list: [[t=LIST0 cid_typ SEP `COMMA -> t]]; *)


expect_option:
 [[
   `OSQUARE; vr = validate_result; `CSQUARE -> vr
 ]];

(**************************************)
(* sat cmd - checksat_cmd *)
(**************************************)
checksat_cmd:
  [[ `CHECKSAT;e = OPT expect_option ;t=meta_constr ->
      (t,e)
  ]];

(**************************************)
(* ent cmd - checkentail_cmd *)
(**************************************)
checkentail_cmd:
  [[ `CHECKENTAIL; e = OPT expect_option; t=meta_constr; `DERIVE; b=meta_constr -> (t, b,  false, e)
   | `CHECKENTAIL_EXACT; e = OPT expect_option; t=meta_constr; `DERIVE; b=meta_constr -> (t, b, true, e)
  ]];

(**************************************)
(*  validate cmd - validate_cmd *)
(**************************************)
validate_cmd:
    [[       pr = validate_cmd_pair; lc = OPT validate_list_context  ->
          let vr,fl = pr in
          (vr, fl, (un_option lc []))
   ]];

ls_rel_ass: [[`OSQUARE; t = LIST0 rel_ass SEP `SEMICOLON ;`CSQUARE-> t]];

rel_ass : [[ t=meta_constr; `CONSTR; b=meta_constr -> (t, b)]];


validate_entail_state:
  [[
     `OPAREN ; `OSQUARE; il1=OPT id_list;`CSQUARE; `COMMA; ef = meta_constr; `COMMA; ls_ass = ls_rel_ass ; `CPAREN->
         let il1 = un_option il1 [] in
         (il1, ef, ls_ass)
  ]];

validate_list_context:
  [[
     `OSQUARE; t = LIST0 validate_entail_state SEP `SEMICOLON ;`CSQUARE-> t
  ]];

validate_result:
  [[
      `IDENTIFIER ex -> Out.UNKNOWN (* ex *)
    | `VALID -> Out.VALID
    | `INVALID -> Out.INVALID
    | `SSAT -> Out.SAT
    | `SUNSAT -> Out.UNSAT
  ]];

validate_cmd_pair:
    [[ `VALIDATE; vr = validate_result  ->
      (vr, None)
      | `VALIDATE; vr = validate_result; `COMMA; fl=OPT id ->
            (vr, fl)
   ]];

(**************************************)
(* composite formula *)
(**************************************)
meta_constr:
  [[ d=disjunctive_constr    -> d ]];

disjunctive_constr:
  [ "disj_or" LEFTA
    [ dc=SELF; `ORWORD; oc=SELF -> IF.mkOr dc oc (get_pos_camlp4 _loc 1)]
  | [ dc=SELF; `ANDWORD; oc=SELF -> dc]
  | [peek_dc; `OPAREN;  dc=SELF; `CPAREN -> dc]
  | "disj_base"
    [ cc=core_constr_and -> cc
    | `EXISTS; ocl= cid_list; `COLON; cc= core_constr_and ->
	  (match cc with
      | IF.Base {
          Isymheap.base_heap = h;
          Isymheap.base_pure = p;
          } ->
        IF.mkExists ocl h p (get_pos_camlp4 _loc 1)
      | IF.Exists  ({
          Isymheap.base_heap = h;
          Isymheap.base_pure = p;
          }, qvars) ->
            let qvars1 =(*  Gen.BList.remove_dups_eq (fun (id1, p1) (id2, p2) -> *)
              (*     Ustr.str_eq id1 id2 *)
              (* ) *) (ocl@qvars) in
            IF.mkExists qvars1 h p (get_pos_camlp4 _loc 1)
      | _ -> report_error (get_pos_camlp4 _loc 4) ("only Base and Exist is expected here."))
    ]
  ];

core_constr_and : [[
    f1 = core_constr -> f1
  | `OPAREN; f1 = core_constr ; `CPAREN-> f1
]];

core_constr:
  [
    [ pc= pure_constr ->
      let pos = (get_pos_camlp4 _loc 1) in
      IF.mkBase Iheap.HTrue pc pos
    | hc= opt_heap_constr;  pc= opt_pure_constr ->
      let pos = (get_pos_camlp4 _loc 1) in
      let qvars = Iheap.get_anon_var hc in
      if qvars = [] then
        IF.mkBase hc pc pos
      else IF.mkExists qvars hc pc pos
    (* | pc= pure_constr ; `AND;  hc= opt_heap_constr-> *)
    (*   let pos = (get_pos_camlp4 _loc 1) in *)
    (*   let qvars = Iheap.get_anon_var hc in *)
    (*   if qvars = [] then *)
    (*     IF.mkBase hc pc pos *)
    (*   else IF.mkExists qvars hc pc pos *)
    ]
  ];

opt_pure_constr:
    [[t=OPT and_pure_constr -> un_option t (IP.mkTrue no_pos)]];

and_pure_constr:
    [[ peek_and_pure; `AND; t= pure_constr ->
        t]];

(**************************************)
(* symbolic heap*)
(**************************************)
opt_heap_constr: [[ t = heap_constr -> t]];

heap_constr:
  [[ shc=heap_rd  -> shc ]];

(* heap_constr: *)
(*   [[ `OPAREN; hrd=heap_rd; `CPAREN; `SEMICOLON; hrw=heap_rw -> *)
(*       F.mkPhase hrd hrw (get_pos_camlp4 _loc 2) *)
(*    | `OPAREN; hrd=heap_rd; `CPAREN                          -> *)
(*          F.mkPhase hrd F.HEmp (get_pos_camlp4 _loc 2) *)
(*    | hrw = heap_rw                                          -> *)
(*          F.mkPhase F.HEmp hrw (get_pos_camlp4 _loc 2)]]; *)


heap_rd:
  [[ shi= simple_heap_constr; `STAR; hrd=SELF -> Iheap.mkStar shi hrd (get_pos_camlp4 _loc 2)
    | shi=simple_heap_constr          -> shi
  ]];


(* heap_rw: *)
(*   [[ hrd=heap_wr; `STAR; `OPAREN; hc=heap_constr; `CPAREN -> *)
(*       F.mkStar hrd hc (get_pos_camlp4 _loc 2) *)
(*     | hwr=heap_wr *)
(*           -> F.mkPhase F.HEmp hwr (get_pos_camlp4 _loc 2)]]; *)

(* heap_wr: *)
(*   [[ *)
(*      shc=SELF; peek_star; `STAR; hw= simple_heap_constr    -> *)
(*          F.mkStar shc hw (get_pos_camlp4 _loc 2) *)
(*    | shc=simple_heap_constr        -> shc *)
(*   ]]; *)

heap_id:
  [[
     `IDENTIFIER id -> (id, 0, 0, _loc)
   (* definitions below is for cparser *)
   | `VOID; `STAR -> ("void", 1, 0, _loc)
   | `INT; `STAR -> ("int", 1, 0, _loc)
   | `FLOAT; `STAR -> ("float", 1, 0, _loc)
   | `DBL; `STAR -> ("double", 1, 0, _loc)
   | `BOOL; `STAR -> ("bool", 1, 0, _loc)
   | `IDENTIFIER id; `STAR -> (id, 1, 0, _loc)
   | `VOID; `CARET -> ("void", 0, 1, _loc)
   | `INT; `CARET -> ("int", 0, 1, _loc)
   | `FLOAT; `CARET -> ("float", 0, 1, _loc)
   | `DBL; `CARET -> ("double", 0, 1, _loc)
   | `BOOL; `CARET -> ("bool", 0, 1, _loc)
   | `IDENTIFIER id; `CARET -> (id, 0, 1, _loc)
   | hid = heap_id; `STAR ->
       let (h, s, c, l) = hid in
       if (c > 0) then
         report_error (get_pos_camlp4 _loc 1) "invalid heap_id string"
       else
         (h, s+1, c, l)
   | hid = heap_id; `CARET ->
       let (h, s, c, l) = hid in
       (h, s, c+1, l)
  ]];

simple_heap_constr:
    [[ peek_heap; c=cid; `COLONCOLON; hid = heap_id;hl = gen_args1; dr=opt_derv ->
        (
        let (c, hid, deref) = get_heap_id_info c hid in
        match hl with
       (* HeapNode2 is for d<field=v*> *)
       (*  p<> can be either node or predicate *)
       | ([],[]) -> Iheap.mkPtoNode c hid deref dr [] (get_pos_camlp4 _loc 2)
       | ([],t) -> Iheap.mkHeapNode2 c hid deref dr t (get_pos_camlp4 _loc 2)
       | (t,_)  -> Iheap.mkPtoNode c hid deref dr  t  (get_pos_camlp4 _loc 2)
     )
      | peek_heap; c=cid; `COLONCOLON; hid = heap_id; hl=data_args2; dr=opt_derv ->
         (
         let (c, hid, deref) = get_heap_id_info c hid in
         match hl with
           | ([],[]) -> Iheap.mkPtoNode c hid deref dr [] (get_pos_camlp4 _loc 2)
           | ([], t) ->
                 let t11, t12 = List.split t in
                 let t21, t22 = List.split t12 in
                 let t3 = List.combine t11 t21 in
                 Iheap.mkHeapNode2 c hid deref dr t3 (*t22*) (get_pos_camlp4 _loc 2)
           | (t, _)  ->
                 let t1, t2 = List.split t in
                 Iheap.mkPtoNode c hid deref dr t1 (* t2 *) (get_pos_camlp4 _loc 2)
     )
   | peek_heap; c=cid; `COLONCOLON; hal = gen_args1; dr=opt_derv -> (
         match hal with
           | ([],[])  -> Iheap.mkPtoNode c generic_pointer_type_name 0 dr [] (get_pos_camlp4 _loc 2)
           | ([],t) -> Iheap.mkHeapNode2 c generic_pointer_type_name 0 dr t (get_pos_camlp4 _loc 2)
           | (t,_)  -> Iheap.mkPtoNode c generic_pointer_type_name 0 dr t (get_pos_camlp4 _loc 2)
     )
   | peek_pred; `IDENTIFIER hid; hl = gen_args_pred; dr=opt_derv ->(
         match hl with
             (*  p<> is predicate *)
           | ([],[]) -> Iheap.mkPredNode  hid 0 dr [] (get_pos_camlp4 _loc 2)
           | (t, _) -> Iheap.mkPredNode  hid 0 dr  t  (get_pos_camlp4 _loc 2)
     )
   | `HTRUE -> Iheap.HTrue
   | `EMPTY -> Iheap.HEmp
  ]];

opt_derv: [[t=OPT derv -> un_option t false ]];

derv : [[ `DERV -> true ]];


(**************************************)
(* pure formula*)
(**************************************)
pure_constr:
  [[ peek_pure_out; t= cexp_w ->
      match t with
       | Pure_f f -> f
       | Pure_c (Iexp.Var (v,_)) ->
             let f = IP.mkBForm (Iterm.mkBVar v (get_pos_camlp4 _loc 1)) in
             f
       | Pure_c (Iexp.Ann_Exp (Iexp.Var (v,_), Bool, _)) ->
             IP.mkBForm (Iterm.mkBVar v (get_pos_camlp4 _loc 1))
       | _ -> report_error (get_pos_camlp4 _loc 1) "expected pure_constr, found cexp"
  ]];

(**************************************)
(* term and exp *)
(**************************************)
cexp_w:
  [ "pure_or" RIGHTA
    [ pc1=SELF; `OR; pc2=SELF ->
        apply_pure_form2 (fun c1 c2 ->
            IP.mkOr c1 c2 (get_pos_camlp4 _loc 2))
            pc1 pc2
    ]
  | "pure_and" RIGHTA
    [ pc1=SELF; peek_and; `AND; pc2=SELF ->
        apply_pure_form2 (fun c1 c2->
            IP.mkAnd c1 c2 (get_pos_camlp4 _loc 2))
            pc1 pc2
    ]
  |"term" RIGHTA
    [ lc=SELF; `NEQ; cl=SELF ->
        cexp_to_pure2 (fun c1 c2 ->
            Iterm.mkNeq c1 c2 (get_pos_camlp4 _loc 2))
          lc cl
    | lc=SELF; `EQ;   cl=SELF  -> begin
        cexp_to_pure2 (fun c1 c2 ->
            Iterm.mkEq c1 c2 (get_pos_camlp4 _loc 2))
            lc cl
    end
    ]
  | "termexp"
    [ lc=SELF; `LTE; cl=SELF ->
        cexp_to_pure2 (fun c1 c2-> Iterm.mkLte c1 c2 (get_pos_camlp4 _loc 2)) lc cl
    | lc=SELF; `LT; cl=SELF ->
        cexp_to_pure2 (fun c1 c2-> Iterm.mkLt c1 c2 (get_pos_camlp4 _loc 2)) lc cl
    | lc=SELF; peek_try; `GT; cl=SELF ->
        cexp_to_pure2 (fun c1 c2-> Iterm.mkGt c1 c2 (get_pos_camlp4 _loc 2)) lc cl
    | lc=SELF; `GTE; cl=SELF ->
        cexp_to_pure2 (fun c1 c2-> Iterm.mkGte c1 c2 (get_pos_camlp4 _loc 2)) lc cl
    | lc=SELF; `IN_T;   cl=SELF ->
        let cid, pos = match lc with
          | Pure_c (Iexp.Var (t, l)) -> (t, l)
          | Pure_c (Iexp.Null l) -> ((null_name, Unprimed), l)
          | _ -> report_error (get_pos_camlp4 _loc 1) "expected cid"
        in
        cexp_to_pure1 (fun c2 -> Iterm.mkBagIn cid c2 pos) cl
    | lc=SELF; `NOTIN;  cl=SELF ->
        let cid, pos = match lc with
          | Pure_c (Iexp.Var (t, l)) -> (t, l)
          | Pure_c (Iexp.Null l) -> ((null_name,Unprimed), l)
          | _ -> report_error (get_pos_camlp4 _loc 1) "expected cid" in
        cexp_to_pure1 (fun c2 -> Iterm.mkBagNotIn cid c2 pos) cl
    | lc=SELF; `SUBSET; cl=SELF ->
        cexp_to_pure2 (fun c1 c2-> Iterm.mkBagSub c1 c2 (get_pos_camlp4 _loc 2))
            lc cl
    | `BAGMAX; `OPAREN; c1=cid; `COMMA; c2=cid; `CPAREN ->
        Pure_f (IP.mkBForm (Iterm.mkBagMax c1 c2 (get_pos_camlp4 _loc 2)))
    | `BAGMIN; `OPAREN; c1=cid; `COMMA; c2=cid; `CPAREN ->
        Pure_f (IP.mkBForm (Iterm.mkBagMin c1 c2 (get_pos_camlp4 _loc 2)))
    ]
  | "pure_parent"
    [ peek_pure; `OPAREN; dc=SELF; `CPAREN -> dc ]
  | "type_casting"
    [ peek_typecast; `OPAREN; t = typ; `CPAREN; c = SELF ->
        apply_cexp_form1 (fun c -> Iexp.mkTypeCast t c (get_pos_camlp4 _loc 1)) c
    ]
  (* expressions *)
  | "allexp"
    [ `OBRACE; c= opt_cexp_list; `CBRACE ->
        Pure_c (Iexp.mkBag c (get_pos_camlp4 _loc 1))
      | `UNION; `OPAREN; c=opt_cexp_list; `CPAREN ->
            Pure_c (Iexp.mkBagUnion c (get_pos_camlp4 _loc 1))
      | `INTERSECT; `OPAREN; c=opt_cexp_list; `CPAREN ->
            Pure_c (Iexp.mkBagIntersect c (get_pos_camlp4 _loc 1))
      | `DIFF; `OPAREN; c1=SELF; `COMMA; c2=SELF; `CPAREN ->
            apply_cexp_form2 (fun c1 c2->
                Iexp.mkBagDiff c1 c2 (get_pos_camlp4 _loc 1))
                c1 c2
    ]
  | "addit"
    [ c1=SELF ; `PLUS; c2=SELF -> apply_cexp_form2 (fun c1 c2->
        Iexp.mkAdd c1 c2 (get_pos_camlp4 _loc 2)) c1 c2
      | c1=SELF ; `MINUS; c2=SELF -> apply_cexp_form2 (fun c1 c2->
            Iexp.mkSubtract c1 c2 (get_pos_camlp4 _loc 2)) c1 c2
    ]
  | "mul"
    [ t1=SELF ; `STAR; t2=SELF -> apply_cexp_form2 (fun c1 c2->
        Iexp.mkMult c1 c2 (get_pos_camlp4 _loc 2)) t1 t2
      | t1=SELF ; `DIV ; t2=SELF -> apply_cexp_form2 (fun c1 c2->
            Iexp.mkDiv c1 c2 (get_pos_camlp4 _loc 2)) t1 t2
    ]
  | [`MINUS; c=SELF -> apply_cexp_form1 (fun c-> Iexp.mkSubtract
        (Iexp.mkIConst 0 (get_pos_camlp4 _loc 1)) c (get_pos_camlp4 _loc 1)) c]
  | "ann_exp"
    [e=SELF ; `COLON; ty=typ -> apply_cexp_form1 (fun c->
        Iexp.mkAnnExp c ty (get_pos_camlp4 _loc 1)) e]
  | "una"
    [ `NULL -> Pure_c (Iexp.mkNull (get_pos_camlp4 _loc 1))
      | `IDENTIFIER id; `OPAREN; cl = opt_cexp_list; `CPAREN ->
      (* relation constraint, for instance, given the relation
       * s(a,b,c) == c = a + b.
       * After this definition, we can have the relation constraint like
       * s(x,1,x+1), s(x,y,x+y), ...
       * in our formula.
       *)
          let () =
            if not (rel_names # mem id ) then
              print_endline ("WARNING : parsing problem "^id^" is not
 a relation nor a heap predicate")
            else ()
          in
          Pure_f(IP.mkBForm (Iterm.mkRelForm id cl (get_pos_camlp4 _loc 1)))
      | t = cid -> Pure_c (Iexp.mkVar t (get_pos_camlp4 _loc 1))
      | `INT_LITER (i,_) -> Pure_c (Iexp.mkIConst i (get_pos_camlp4 _loc 1))
      | `FLOAT_LIT (f,_) -> Pure_c (Iexp.mkFConst f (get_pos_camlp4 _loc 1))
      | `OPAREN; t=SELF; `CPAREN -> t
      | i=cid; `OSQUARE; c = LIST1 cexp SEP `COMMA; `CSQUARE ->
            Pure_c (Iexp.mkArrayAt i c (get_pos_camlp4 _loc 1))
      | `MAX; `OPAREN; c1=SELF; `COMMA; c2=SELF; `CPAREN ->
            apply_cexp_form2 (fun c1 c2->
                Iexp.mkMax c1 c2 (get_pos_camlp4 _loc 1)) c1 c2
      | `MIN; `OPAREN; c1=SELF; `COMMA; c2=SELF; `CPAREN ->
            apply_cexp_form2 (fun c1 c2->
                Iexp.mkMin c1 c2 (get_pos_camlp4 _loc 1)) c1 c2
    ]
  | "pure_base"
          [ `TRUE -> Pure_f (IP.mkTrue (get_pos_camlp4 _loc 1))
            | `FALSE -> Pure_f (IP.mkFalse (get_pos_camlp4 _loc 1))
            | `EXISTS; `OPAREN; ocl=opt_cid_list; `COLON; pc = SELF; `CPAREN ->
                  apply_pure_form1 (fun c-> List.fold_left (fun f v ->
                      IP.mkExists [v] f (get_pos_camlp4 _loc 1)) c ocl) pc
    | `FORALL; `OPAREN; ocl=opt_cid_list; `COLON; pc=SELF; `CPAREN ->
        apply_pure_form1 (fun c-> List.fold_left (fun f v->
            IP.mkForall [v] f (get_pos_camlp4 _loc 1)) c ocl) pc
    | t=cid ->
          Pure_f (IP.mkBForm (Iterm.mkBVar t (get_pos_camlp4 _loc 1)))
    | `NOT; `OPAREN; c=pure_constr; `CPAREN ->
          Pure_f (IP.mkNot c (get_pos_camlp4 _loc 1))
    | `NOT; t=cid -> Pure_f (IP.mkNot
          (IP.mkBForm (Iterm.mkBVar t (get_pos_camlp4 _loc 2)))
          (get_pos_camlp4 _loc 1))
    ]
  ];

opt_cexp_list: [[t=LIST0 cexp SEP `COMMA -> t]];

cexp :
    [[t = cexp_data_p -> match t with
      | f, _ ->  f
    ]];


cexp_data_p:
    [[t = cexp_w -> match t with
      | Pure_c f -> (f, None)
      | _ -> report_error (get_pos_camlp4 _loc 1) "3 expected cexp, found pure_constr"
    ]
    ];


END;;


(* let parse_sl_int n s = *)
(*   SLGram.parse_string sprog_int (PreCast.Loc.mk n) s *)

let parse_sl n s =
  SLGram.parse sprog (PreCast.Loc.mk n) s


(* let parse_sl n s = *)
(*   DD.no_1 "parse_sl" (fun x -> x) (pr_list Cmd.string_of) (fun n -> parse_sl n s) n *)
