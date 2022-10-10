open Camlp4
open Token

open VarGen

module DD=Debug

module SLGram = Camlp4.Struct.Grammar.Static.Make(Lexer.Make(Token))

let pred_names: string Gen.stack = new Gen.stack (* list of names of pred declared *)
let rel_names: string Gen.stack = new Gen.stack (* list of names of relations declared *)
let hp_names: string Gen.stack = new Gen.stack (* list of names of pred declared *)


(* Use the Stream.npeek to look ahead the TOKENS *)
let peek_try = 
 SLGram.Entry.of_parser "peek_try" 
    (fun strm -> 
       match Stream.npeek 2 strm with 
         | [_;IN_T,_]  -> ()
         | [_;NOTIN,_] -> ()
	 | [GT,_; CBRACE,_] -> raise Stream.Failure
         | [SEMICOLON,_; CBRACE,_] -> raise Stream.Failure
         | [OPAREN,_; EXISTS,_ ] -> raise Stream.Failure
         | [GT,_;STAR,_] -> raise Stream.Failure
         | [GT,_;STARMINUS,_] -> raise Stream.Failure
         | [GT,_;INV,_] -> raise Stream.Failure
         | [GT,_;INV_EXACT,_] -> raise Stream.Failure
         | [GT,_;INV_SAT,_] -> raise Stream.Failure
         | [GT,_;AND,_] -> raise Stream.Failure
         | [GT,_;ANDSTAR,_] -> raise Stream.Failure
         | [GT,_;UNIONSTAR,_] -> raise Stream.Failure
         | [GT,_;ANDAND,_] -> raise Stream.Failure
         | [GT,_;OR,_] -> raise Stream.Failure
         | [GT,_;ORWORD,_] -> raise Stream.Failure
         | [GT,_;DOT,_] -> raise Stream.Failure
         | [GT,_;DERIVE,_] -> raise Stream.Failure
         | [GT,_;EQV,_] -> raise Stream.Failure
	 | [GT,_;CONSTR,_] -> raise Stream.Failure
         | [GT,_;LEFTARROW,_] -> raise Stream.Failure
         | [GT,_;RIGHTARROW,_] -> raise Stream.Failure
         | [GT,_;EQUIV,_] -> raise Stream.Failure
         | [GT,_;CPAREN,_] -> raise Stream.Failure
         | [GT,_;SEMICOLON,_]-> raise Stream.Failure
         | [GT,_;ENSURES,_]-> raise Stream.Failure
         | [GT,_;ENSURES_EXACT,_]-> raise Stream.Failure
         | [GT,_;ENSURES_INEXACT,_]-> raise Stream.Failure
         | [GT,_;AT,_] -> raise Stream.Failure
         | [GT,_;MUT,_] -> raise Stream.Failure
	 | [GT,_;MAT,_] -> raise Stream.Failure
         | [GT,_;DERV,_] -> raise Stream.Failure
         | [GT,_;CASE,_] -> raise Stream.Failure
         | [GT,_;VARIANCE,_] -> raise Stream.Failure
         | [GT,_;_] -> ()
         | [SEMICOLON,_;_] -> ()
         | _ -> raise Stream.Failure  )

 let peek_try_st =
 SLGram.Entry.of_parser "peek_try_st"
     (fun strm ->
       match Stream.npeek 2 strm with
          | [_; OP_DEC,_] -> ()
          | _ -> raise Stream.Failure)

 let peek_try_st_in = 
 SLGram.Entry.of_parser "peek_try_st_in"
     (fun strm ->
       match Stream.npeek 2 strm with
          | [_; OP_INC,_] -> ()
          | _ -> raise Stream.Failure)

 let peek_try_st_qi =
 SLGram.Entry.of_parser "peek_try_st_qi"
     (fun strm ->
       match Stream.npeek 2 strm with
          | [_; DOT,_] -> ()
          | _ -> raise Stream.Failure
     )

 let peek_invocation =
 SLGram.Entry.of_parser "peek_invocation"
     (fun strm ->
       match Stream.npeek 5 strm with
          | [_; OPAREN,_;_;_;_] -> ()
          | [_; OSQUARE,_; _; CSQUARE, _ ; OPAREN,_] -> ()
          | _ -> raise Stream.Failure
     )

 let peek_member_name =
 SLGram.Entry.of_parser "peek_member_name"
     (fun strm ->
       match Stream.npeek 2 strm with
          | [IDENTIFIER n,_;DOT,_] -> raise Stream.Failure
          | _ -> ()
     )

 let peek_exp_st =
 SLGram.Entry.of_parser "peek_exp_st"
     (fun strm ->
       match Stream.npeek 1 strm with
          | [DPRINT,_] -> raise Stream.Failure
          | _ -> ())

 let peek_try_declarest =
 SLGram.Entry.of_parser "peek_try_declarest"
     (fun strm ->
       match Stream.npeek 2 strm with
          | [_;EQ,_] -> raise Stream.Failure
          | [CONST,_;_] -> ()
          | [INT,_;IDENTIFIER n,_] -> ()
          | [FLOAT,_;IDENTIFIER n,_] -> ()
          | [DBL,_;IDENTIFIER n,_] -> ()
          | [BOOL,_;IDENTIFIER n,_] -> ()
          | [IDENTIFIER n,_;IDENTIFIER id,_] -> ()
          | [INT,_;OSQUARE,_] -> ()
          | [FLOAT,_;OSQUARE,_] -> ()
          | [DBL,_;OSQUARE,_] -> ()
          | [BOOL,_;OSQUARE,_] -> ()
          (* For pointer*)
          | [INT,_;STAR,_] -> ()
          | [FLOAT,_;STAR,_] -> ()
          | [DBL,_;STAR,_] -> ()
          | [BOOL,_;STAR,_] -> ()
          | [IDENTIFIER n,_;STAR,_] -> ()
          |  _ -> raise Stream.Failure)

let peek_print =
SLGram.Entry.of_parser "peek_print"
	(fun strm ->
		match Stream.npeek 3 strm with
		| [i,_;j,_;k,_]-> print_string((Token.to_string i)^" "^(Token.to_string j)^" "^(Token.to_string k)^"\n");()
		| _ -> raise Stream.Failure)

(*This is quite similar to peek_and_pure*)
 let peek_and =
   SLGram.Entry.of_parser "peek_and"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [AND,_;FLOW i,_;_] -> raise Stream.Failure
             | [AND,_;OSQUARE,_;STRING _,_] -> raise Stream.Failure
             | _ -> ())

 let peek_pure =
   SLGram.Entry.of_parser "peek_pure"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [FORALL,_;OPAREN,_;_] -> ()
             | [EXISTS,_;OPAREN,_;_] -> ()
             | [UNION,_;OPAREN,_;_] -> ()
             | [IDENTIFIER id,_;OPAREN,_;_] -> ()
             | [_;COLONCOLON,_;_] -> raise Stream.Failure
             | [_;OPAREN,_;_] -> raise Stream.Failure
             | [_;PRIME,_;COLONCOLON,_] -> raise Stream.Failure
             | [OPAREN,_;_;COLONCOLON,_] -> raise Stream.Failure
             | _ -> ())

 let peek_pure_out =
   SLGram.Entry.of_parser "peek_pure_out"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [FORALL,_;OPAREN,_;_] -> ()
             | [EXISTS,_;OPAREN,_;_] -> ()
             | [UNION,_;OPAREN,_;_] -> ()
	     | [IDENTIFIER id,_;OPAREN,_;_] ->  (*if hp_names # mem id || pred_names # mem id then*) raise Stream.Failure (* else () *)
             (*| [IDENTIFIER id,_;LT,_;_] ->  if pred_names # mem id then raise Stream.Failure else ()*)
             | [_;COLONCOLON,_;_] -> raise Stream.Failure
             | [_;PRIME,_;COLONCOLON,_] -> raise Stream.Failure
             | [OPAREN,_;_;COLONCOLON,_] -> raise Stream.Failure
             | [OSQUARE,_;_;COLONCOLON,_] -> raise Stream.Failure
             | [OSQUARE,_;DOUBLEQUOTE,_;_]-> raise Stream.Failure
             | _ -> ())

 let peek_typecast =
   SLGram.Entry.of_parser "peek_typecast"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [OPAREN,_;VOID,_;CPAREN, _] -> ()
             | [OPAREN,_;INT,_;CPAREN, _] -> ()
             | [OPAREN,_;FLOAT,_;CPAREN, _] -> ()
             | [OPAREN,_;DBL,_;CPAREN, _] -> ()
             | [OPAREN,_;BOOL,_;CPAREN, _] -> ()
             | [OPAREN,_;BAG,_;CPAREN, _] -> ()
             | [OPAREN,_;IDENTIFIER id,_;CPAREN, _] -> ()
             | [OPAREN,_;REL,_; _] -> ()
             | [OPAREN,_;_;OSQUARE,_] -> () (* array type cast *)
             | [OPAREN,_;_;STAR,_] -> ()   (* pointer type cast *)
             | _ -> raise Stream.Failure)

let peek_dc =
   SLGram.Entry.of_parser "peek_dc"
       (fun strm ->
           match Stream.npeek 2 strm with
             | [OPAREN,_;EXISTS,_] -> ()
             | _ -> raise Stream.Failure)

(*This seems similar to peek_and*)
 let peek_and_pure =
   SLGram.Entry.of_parser "peek_and_pure"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [AND,_;FLOW i,_;_] -> raise Stream.Failure
             | [AND,_;OSQUARE,_;STRING _,_] -> raise Stream.Failure
             | _ -> ())

 let peek_view_decl =
   SLGram.Entry.of_parser "peek_heap_args"
       (fun strm -> 
           match Stream.npeek 3 strm with
             | [PRED,_;IDENTIFIER n,_;LT,_] ->  ()
             | [IDENTIFIER n,_;LT,_;_] ->  ()
             (* | [IDENTIFIER n,_;OBRACE,_] ->  () (\*This is for prim_view_decl*\) *)
             | _ -> raise Stream.Failure)

 let peek_heap_args =
   SLGram.Entry.of_parser "peek_heap_args"
       (fun strm ->
           match Stream.npeek 2 strm with
             | [IDENTIFIER n,_;EQ,_] ->  ()
             | _ -> raise Stream.Failure)

let peek_hash_thread =
   SLGram.Entry.of_parser "peek_hash_thread"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [_;_;COMMA,_] ->  raise Stream.Failure
             | [_;_;GT,_] ->  raise Stream.Failure
             | _ -> ())

 let peek_extended =
   SLGram.Entry.of_parser "peek_extended"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [OSQUARE,_;_;ORWORD,_] -> ()
             | _ -> raise Stream.Failure)

 let peek_div_op =
   SLGram.Entry.of_parser "peek_div_op"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [_;DIV,_;_] -> ()
             | ls -> raise Stream.Failure)

 let peek_cexp_list =
   SLGram.Entry.of_parser "peek_cexp_list"
       (fun strm ->
           match Stream.npeek 6 strm with
             | [_;COMMA,_;_;GTE,_;_;_] -> ()
             | [_;COMMA,_;_;AND,_;_;_] -> ()
             | [_;COMMA,_;_;COMMA,_;_;SEMICOLON,_] -> ()
             | _ -> raise Stream.Failure)

 let peek_heap =
   SLGram.Entry.of_parser "peek_heap"
       (fun strm ->
           match Stream.npeek 3 strm with
             |[_;COLONCOLON,_;_] -> ()
             |[_;PRIME,_;COLONCOLON,_] -> ()
             |[EMPTY,_;_;_] -> ()
             |[_;EMPTY,_;_] -> ()
             |[_;_;EMPTY,_] -> ()
             |[HTRUE,_;_;_] -> ()
             |[_;HTRUE,_;_] -> ()
             |[_;_;HTRUE,_] -> ()
             | _ -> raise Stream.Failure)

 let peek_pred =
   SLGram.Entry.of_parser "peek_pred"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [_;COLONCOLON,_;_] -> raise Stream.Failure
             | [_;EMPTY,_;_] -> raise Stream.Failure
             | _ -> ()
       )

let peek_star =
   SLGram.Entry.of_parser "peek_star"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [AND,_;IDENTIFIER id,_; COLONCOLON,_] -> raise Stream.Failure
             | [STAR,_;OPAREN,_;_] -> raise Stream.Failure
             | _ -> ())

let peek_heap_and =
   SLGram.Entry.of_parser "peek_heap_and"
       (fun strm ->
           match Stream.npeek 4 strm with
             |[AND,_;OPAREN ,_; IDENTIFIER id,_; COLONCOLON,_] -> ()
             |[AND,_;IDENTIFIER id,_; COLONCOLON,_; _,_] -> ()
             |[AND,_;SELFT t,_; COLONCOLON,_; _,_] -> ()
             |[AND,_;THIS t,_; COLONCOLON,_; _,_] -> ()
             |[AND,_;RES t,_; COLONCOLON,_; _,_] -> ()
             | _ -> raise Stream.Failure)

let peek_heap_andstar =
   SLGram.Entry.of_parser "peek_heap_andstar"
       (fun strm ->
           match Stream.npeek 4 strm with
             |[ANDSTAR,_;OPAREN ,_; IDENTIFIER id,_; COLONCOLON,_] -> ()
             |[ANDSTAR,_;IDENTIFIER id,_; COLONCOLON,_; _,_] -> ()
             |[ANDSTAR,_;SELFT t,_; COLONCOLON,_; _,_] -> ()
             |[ANDSTAR,_;THIS t,_; COLONCOLON,_; _,_] -> ()
             |[ANDSTAR,_;RES t,_; COLONCOLON,_; _,_] -> ()
             | _ -> raise Stream.Failure)

let peek_heap_unionstar =
   SLGram.Entry.of_parser "peek_heap_unionstar"
       (fun strm ->
           match Stream.npeek 4 strm with
             |[UNIONSTAR,_;OPAREN ,_; IDENTIFIER id,_; COLONCOLON,_] -> ()
             |[UNIONSTAR,_;IDENTIFIER id,_; COLONCOLON,_; _,_] -> ()
             |[UNIONSTAR,_;SELFT t,_; COLONCOLON,_; _,_] -> ()
             |[UNIONSTAR,_;THIS t,_; COLONCOLON,_; _,_] -> ()
             |[UNIONSTAR,_;RES t,_; COLONCOLON,_; _,_] -> ()
             | _ -> raise Stream.Failure)

let peek_heap_starminus =
   SLGram.Entry.of_parser "peek_heap_starminus"
       (fun strm ->
           match Stream.npeek 4 strm with
             |[STARMINUS,_;OPAREN ,_; IDENTIFIER id,_; COLONCOLON,_] -> ()
             |[STARMINUS,_;IDENTIFIER id,_; COLONCOLON,_; _,_] -> ()
             |[STARMINUS,_;SELFT t,_; COLONCOLON,_; _,_] -> ()
             |[STARMINUS,_;THIS t,_; COLONCOLON,_; _,_] -> ()
             |[STARMINUS,_;RES t,_; COLONCOLON,_; _,_] -> ()
             | _ -> raise Stream.Failure)

let peek_array_type =
   SLGram.Entry.of_parser "peek_array_type"
       (fun strm ->
           match Stream.npeek 2 strm with
             |[_;OSQUARE,_] -> ()
             | _ -> raise Stream.Failure)

let peek_pointer_type =
   SLGram.Entry.of_parser "peek_pointer_type"
       (fun strm ->
           match Stream.npeek 2 strm with
             |[_;STAR,_] -> ()
             | _ -> raise Stream.Failure)

let peek_obrace_par =
  SLGram.Entry.of_parser "peek_obrace_par"
    (fun strm ->
      match Stream.npeek 2 strm with
      | [OBRACE,_;CASE,_] -> raise Stream.Failure
      | _ -> ())

let peek_relassume =
  SLGram.Entry.of_parser "peek_relassume"
    (fun strm ->
      match Stream.npeek 1 strm with
      | [IDENTIFIER "RA",_] -> raise Stream.Failure
      | _ -> ())
