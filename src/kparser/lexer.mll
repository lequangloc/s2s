{
open Globals

open Token
(** A signature for specialized tokens. *)
module Sig = Camlp4.Sig

module Make (Token : KTokenS) 
= struct
  module Loc = Token.Loc
  module Token = Token

  open Lexing
  

  (* Error report *)
  module Error = struct

    type t =
      | Illegal_character of char
      | Illegal_escape    of string
      | Unterminated_comment
      | Unterminated_string
      | Unterminated_java
      | Comment_start
      | Comment_not_end
      | Literal_overflow of string

    exception E of t

    open Format

    let print ppf =
      function
      | Illegal_character c -> fprintf ppf "Illegal character (%s)" (Char.escaped c)
      | Illegal_escape s -> fprintf ppf "Illegal backslash escape in string or character (%s)" s
      | Unterminated_comment -> fprintf ppf "Comment not terminated"
      | Unterminated_string -> fprintf ppf "String literal not terminated"
      | Unterminated_java -> fprintf ppf "java code not terminated"
      | Literal_overflow ty -> fprintf ppf "Integer literal exceeds the range of representable integers of type %s" ty
      | Comment_start -> fprintf ppf "this is the start of a comment"
      | Comment_not_end -> fprintf ppf "this is not the end of a comment"

    let to_string x =
      let b = Buffer.create 50 in
      let () = bprintf b "%a" print x in Buffer.contents b
  end;;

  let module M = Camlp4.ErrorHandler.Register(Error) in ()

  open Error

  type context =
  { loc        : Loc.t    ;
    in_comment : bool     ;
    lexbuf     : lexbuf   ;
    buffer     : Buffer.t }

  let default_context lb =
  { loc        = Loc.ghost ;
    in_comment = false     ;
    lexbuf     = lb        ;
    buffer     = Buffer.create 256 }

  (* To buffer string literals *)

  let store c = Buffer.add_string c.buffer (Lexing.lexeme c.lexbuf)
  let istore_char c i = Buffer.add_char c.buffer (Lexing.lexeme_char c.lexbuf i)
  let buff_contents c =
    let contents = Buffer.contents c.buffer in
    Buffer.reset c.buffer; contents

  let loc c = Loc.merge c.loc (Loc.of_lexbuf c.lexbuf)
  let is_in_comment c = c.in_comment
  let in_comment c = { (c) with in_comment = true }
  let set_start_p c = c.lexbuf.lex_start_p <- Loc.start_pos c.loc
  let move_start_p shift c =
    let p = c.lexbuf.lex_start_p in
    c.lexbuf.lex_start_p <- { (p) with pos_cnum = p.pos_cnum + shift }

  let update_loc c = { (c) with loc = Loc.of_lexbuf c.lexbuf }
  let with_curr_loc f c = f (update_loc c) c.lexbuf
  let parse_nested f c =   with_curr_loc f c;   set_start_p c;    buff_contents c
  let shift n c = { (c) with loc = Loc.move `both n c.loc }
  let store_parse f c = store c ; f c c.lexbuf
  let parse f c = f c c.lexbuf

  (* Update the current location with file name and line number. *)

  let update_loc c file line absolute chars =
    let lexbuf = c.lexbuf in
    let pos = lexbuf.lex_curr_p in
    let new_file = match file with
                  | None -> pos.pos_fname
                  | Some s -> s  in
    lexbuf.lex_curr_p <- { pos with
      pos_fname = new_file;
      pos_lnum = if absolute then line else pos.pos_lnum + line;
      pos_bol = pos.pos_cnum - chars;
    }

  let err error loc = raise(Loc.Exc_located(loc, Error.E error))

  let warn error loc = Format.eprintf "Warning: %a: %a@." Loc.print loc Error.print error

 let k_keywords = Hashtbl.create 100
 let comment_level = ref 0
 let _ = List.map (fun ((k,t):(string*k_token)) -> Hashtbl.add k_keywords k t)
   [("assert", ASSERT);
   ("assert_exact", ASSERT_EXACT);
   ("at", ATPOS);
   ("assert_inexact", ASSERT_INEXACT);
   ("assume", ASSUME);
   ("axiom", AXIOM);
   ("alln", ALLN);
   ("app", APPEND);
   ("AndList", ANDLIST);
   ("bagmax", BAGMAX);
   ("bagmin", BAGMIN);
   ("bag", BAG);
   ("Barrier", BARRIER);
   ("bind", BIND);
   ("bool", BOOL);
   ("break", BREAK);
   ("case",CASE);
   ("catch", CATCH);
   ("checkent", CHECKENTAIL);
   ("checkent_exact", CHECKENTAIL_EXACT);
   ("checkent_inexact", CHECKENTAIL_INEXACT);
   ("checksat", CHECKSAT);
   ("relAssume", RELASSUME);
   ("relDefn", RELDEFN);
   ("infer_exact", INFER_EXACT);
   ("infer_inexact", INFER_INEXACT);
   ("capture_residue", CAPTURERESIDUE);
   ("class", CLASS);
   ("compose", COMPOSE);
   ("combine", COMBINE);
   ("const", CONST);
   ("continue", CONTINUE);
   ("ddata", DATA);
   ("debug", DDEBUG);
   ("diff", DIFF);
   ("dynamic", DYNAMIC);
   ("else", ELSE_TT);
   ("emp", EMPTY);
   ("ensures", ENSURES);
   ("ensures_exact", ENSURES_EXACT);
   ("ensures_inexact", ENSURES_INEXACT);
   ("enum", ENUM);
   ("exists", EXISTS);
   ("extends", EXTENDS);
   ("false", FALSE);
   ("finalizes", FINALIZE);
   ("finally", FINALLY);
   ("float", FLOAT);
   ("double", DBL);
   ("forall", FORALL);
   ("ranking", FUNC);
   ("global",GLOBAL);
   ("logical", LOGICAL);
   (* ("head",HEAD); *)
   ("htrue", HTRUE);
   ("if", IF);
   ("in_t", IN_T);
   ("infer", INFER);
   ("inline", INLINE);
  (* ("inlist", INLIST); *)
   ("int", INT);
   ("char",INT);
   ("intersect", INTERSECT);
	 ("inv", INV);
         ("inv_exact", INV_EXACT);
         ("inv_sat", INV_SAT);
         ("BG", BG);
   	 ("lemma", LEMMA TLEM);
	 ("lemma_prop", LEMMA TLEM_PROP);
	 ("lemma_split", LEMMA TLEM_SPLIT);
	 ("lemma_test", LEMMA TLEM_TEST);
	 ("lemma_test_new", LEMMA TLEM_TEST_NEW);
	 ("lemma_unsafe", LEMMA TLEM_UNSAFE);
         ("lemma_safe", LEMMA TLEM_SAFE);
	 ("lemma_infer", LEMMA TLEM_INFER);
         ("lemma_infer_pred", LEMMA TLEM_INFER_PRED);
	 ("len", LENGTH);
	 ("let", LET);
	 ("max", MAX);
	 ("min", MIN);
	 ("new", NEW);
	 ("notin", NOTIN);
   ("notinlist", NOTINLIST);
   ("null", NULL);
   ("off", OFF);
   ("on", ON);
   ("or", ORWORD);
   ("and", ANDWORD);
   ("macro",PMACRO);
   ("pred", PRED);
   ("spec", SPEC);
   ("pred_prim", PRED_PRIM);
   ("pred_extn", PRED_EXT);
   ("print", PRINT);
   ("print_lemmas", PRINT_LEMMAS);
   ("mem", MEM);
   ("memE", MEME);
   ("dprint", DPRINT);
   ("raise", RAISE);
   ("relation", REL);
   ("requires", REQUIRES);
   ("refines", REFINES);
   ("res", RES "res");
   ("rev",REVERSE);
   ("return", RETURN);
   (* ("self", SELFT "self"); *)
   ("set",SET);
   ("split", SPLIT);
   ("subset", SUBSET);
   ("static", STATIC);
   ("tail",TAIL);
   ("then", THEN);
   ("this", THIS "this");
   ("time", DTIME);
   ("throws", THROWS);
   ("to", TO);
   ("true", TRUE);
   ("try", TRY);
   ("unfold", UNFOLD);
   ("union", UNION);
   ("expect", VALIDATE);
   ("valid", VALID);
   ("invalid", INVALID);
   ("sat", SSAT);
   ("unsat", SUNSAT);
   ("Fail", FAIL);
   ("Fail_Must", FAIL_MUST);
   ("Fail_May", FAIL_MAY);
   ("void", VOID);
   ("while", WHILE);
   ("with", WITH);
        ]
}


  let newline = ('\010' | '\013' | "\013\010")
  let blank = [' ' '\009' '\012']
  let alpha = ['a'-'z' 'A'-'Z' '\223'-'\246' '\248'-'\255' '_']
  let identchar = ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '0'-'9']
  let identseq = alpha identchar* (* An Hoa : a single identifier *)
	let ident = (identseq | identseq ''') ('.' identseq)* (* An Hoa : a {possibly} extended quantifier *)
  let locname = ident
  let not_star_symbolchar = ['$' '!' '%' '&' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~' '\\']
  let symbolchar = '*' | not_star_symbolchar
  let hexa_char = ['0'-'9' 'A'-'F' 'a'-'f']
  let decimal_literal = ['0'-'9'] ['0'-'9' '_']*
  let hex_literal = '0' ['x' 'X'] hexa_char ['0'-'9' 'A'-'F' 'a'-'f' '_']*
  let oct_literal = '0' ['o' 'O'] ['0'-'7'] ['0'-'7' '_']*
  let bin_literal = '0' ['b' 'B'] ['0'-'1'] ['0'-'1' '_']*
  let int_literal = decimal_literal | hex_literal | oct_literal | bin_literal
  let float_literal = ['0'-'9'] ['0'-'9' '_']* ('.') ['0'-'9' '_']+  (['e' 'E'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']*)?
  
rule tokenizer file_name = parse
  | newline                            { update_loc file_name None 1 false 0; tokenizer file_name lexbuf }
  | blank+                                                  { tokenizer file_name lexbuf }
  | int_literal as i
        { try  INT_LITER(int_of_string i, i)
          with Failure _ -> err (Literal_overflow "int") (Loc.of_lexbuf lexbuf) }
  | float_literal as f
        { try  FLOAT_LIT(float_of_string f, f)
          with Failure _ -> err (Literal_overflow "float") (Loc.of_lexbuf lexbuf) }
  | (int_literal as i) "l"
        { try  INT_LITER(int_of_string i, i) (*can try different converter if needed*)
          with Failure _ -> err (Literal_overflow "int32") (Loc.of_lexbuf lexbuf) }
  | (int_literal as i) "L"
        { try  INT_LITER(int_of_string i, i) (*can try different converter if needed*)
          with Failure _ -> err (Literal_overflow "int64") (Loc.of_lexbuf lexbuf) }
  | (int_literal as i) "n"
        { try INT_LITER(int_of_string i, i) (*can try different converter if needed*)
          with Failure _ -> err (Literal_overflow "nativeint") (Loc.of_lexbuf lexbuf) }
  | "'\\" (_ as c)
        { err (Illegal_escape (String.make 1 c)) (Loc.of_lexbuf lexbuf)         }
  | "/*" { comment_level := 0; comment file_name lexbuf }
  | "//" { line_comment file_name lexbuf }
  | "/*/"
        { warn Comment_start (Loc.of_lexbuf lexbuf);   
          comment_level := 0;
          comment file_name lexbuf}
  | "*/"
        { warn Comment_not_end (Loc.of_lexbuf lexbuf)                           ;
          move_start_p (-1) file_name; STAR                                      }
  | '"'
        { with_curr_loc string file_name;
          let s = buff_contents file_name in STRING (Camlp4.Struct.Token.Eval.string s, s)     }
  | "'" (newline as x) "'"
        { update_loc file_name None 1 false 1; CHAR_LIT (Camlp4.Struct.Token.Eval.char x, x)       }
  | "'" ( [^ '\\' '\010' '\013']
            | '\\' (['\\' '"' 'n' 't' 'b' 'r' ' ' '\'']
                |['0'-'9'] ['0'-'9'] ['0'-'9']
                |'x' hexa_char hexa_char)
          as x) "'"                                { CHAR_LIT (Camlp4.Struct.Token.Eval.char x, x) }
  | "@A" { ACCS }  
  | '&' { AND }
  | "&*" { ANDSTAR }
  | "&&" { ANDAND }
  | "U*" { UNIONSTAR }
  | "-*" { STARMINUS }
  | "@" { AT }
  | "@@" { ATAT }
  | "@@[" { ATATSQ }
  | "@S" { SAT }
  (* | "@VAL" {VAL} *)
  | "@C" {PASS_COPY}
  | "@R" {PASS_REF}
  | "ref" {PASS_REF2}
  (* | "@REC" {REC} *)
  | "@NI" {NI}
  | "@RO" {RO}
  | "@value" {PVALUE}
  | '^' { CARET }
  | '}' { CBRACE }
  | "|]" {CLIST}
  | ':' { COLON }
  | "::" { COLONCOLON }
  | ":::" { COLONCOLONCOLON }
  | ',' { COMMA }
  | ')' { CPAREN }
  | ']' { CSQUARE }
  | '$' { DOLLAR }
  | "." { DOT }
  | ".." { DOTDOT }
  | "\"" { DOUBLEQUOTE }
  | "\\inf" {INFINITY}
  | "=" { EQ }
  | "==" { EQEQ }
  | "==>" { ESCAPE }
  | "<-" { RIGHTARROW }
  | "<->" { EQUIV }
  | '>' { GT }
  | ">=" { GTE }
  | '#' { HASH }
  | "|#|" {REL_GUARD}
  | "->" { LEFTARROW }
  | '<' { LT }
  | "<=" { LTE }
  | "-" { MINUS }
  | "!=" { NEQ }
  | "!" { NOT }
  | '{' { OBRACE }
  | "[|" {OLIST}
  | '(' { OPAREN }
  | "+=" { OP_ADD_ASSIGN }
  | "--" { OP_DEC }
  | "/=" { OP_DIV_ASSIGN }
  | "++" { OP_INC }
  | "%=" { OP_MOD_ASSIGN }
  | "*=" { OP_MULT_ASSIGN }
  | "-=" { OP_SUB_ASSIGN }
  | '|' { OR }
  | "||" { OROR }
  | "|-" { (* (print_string "der\n"; *)DERIVE }
  | "-|-" { EQV }
  | "-->" { CONSTR }
  | "<#" { TOPAREN }
  | "#>" { TCPAREN } (*Open and close paren for thread heap*)
  | '[' { OSQUARE }
  | '%' { PERCENT }
  | '+' { PLUS }
  | '\'' { PRIME }
  | ';' { SEMICOLON }
  | '*' { STAR }
  | "<:" { SUBANN }
  | '/' { DIV }
  | ident as idstr 
	  {
		if idstr = "_" then
		  IDENTIFIER (qvar_id ^ fresh_trailer ())
		  (* IDENTIFIER ("Anon" ^ fresh_trailer ()) *)
		else if idstr = "java" then begin
      store file_name; JAVA (parse_nested java file_name)
		end else
		  try Hashtbl.find k_keywords idstr
		  with | _ -> IDENTIFIER idstr
	  }
  | eof
      { let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <- { pos with pos_bol  = pos.pos_bol  + 1 ;
                                        pos_cnum = pos.pos_cnum + 1 }; EOF      }
    | _ as c                 { err (Illegal_character c) (Loc.of_lexbuf lexbuf) }

(* search for the first open brace following java keyword *)
and java file_name = parse 
  | "{"   { store file_name; with_curr_loc java file_name; parse java file_name }
  | "}"                                                         {store file_name}
  | ident                                          { store_parse java file_name }
  | eof                                  { err Unterminated_java (loc file_name)}
  | newline    { update_loc file_name None 1 false 0; store_parse java file_name}
  | _                                              { store_parse java file_name }
  
and comment file_name = parse
  | "*/" { 
	  if !comment_level = 0 then
		tokenizer file_name lexbuf 
	  else begin
		comment_level := !comment_level - 1;
		comment file_name lexbuf
	  end	}
  | "/*" {
	  comment_level := !comment_level + 1;
	  comment file_name lexbuf}
  | newline { update_loc file_name None 1 false 0; comment file_name lexbuf }
  | _  { comment file_name lexbuf }

and line_comment file_name = parse
  | newline { update_loc file_name None 1 false 0; tokenizer file_name lexbuf }
  | _ { line_comment file_name lexbuf }
  

and string c = parse
      '"'                                                       { set_start_p c }
    | '\\' newline ([' ' '\t'] * as space)
        { update_loc c None 1 false (String.length space);
          store_parse string c                                                  }
    | '\\' ['\\' '"' 'n' 't' 'b' 'r' ' ' '\'']           { store_parse string c }
    | '\\' ['0'-'9'] ['0'-'9'] ['0'-'9']                 { store_parse string c }
    | '\\' 'x' hexa_char hexa_char                       { store_parse string c }
    | '\\' (_ as x)
        { if is_in_comment c
          then store_parse string c
          else begin
            warn (Illegal_escape (String.make 1 x)) (Loc.of_lexbuf lexbuf);
            store_parse string c
          end }
    | newline
      { update_loc c None 1 false 0; store_parse string c                       }
    | eof                                     { err Unterminated_string (loc c) }
    | _                                                  { store_parse string c } 
 

and preprocess file_name = parse
  | "import" 
      {
		(* processing import *)
		let _ = rip_ws lexbuf in
		let tmp_file_name = get_file_name lexbuf in
		let f1 = String.sub tmp_file_name 1 (String.length tmp_file_name - 2) in
		let in_file = open_in f1 in
		let cont = ref true in
		let in_cont = Buffer.create 1024 in
		  while !cont do
			try
			  let line = input_line in_file in
				Buffer.add_string in_cont (line ^ "\n")
			with
			  | End_of_file -> cont := false
		  done;
		  output_string file_name (Buffer.contents in_cont);
		  preprocess file_name lexbuf
      }
  | _ as c 
      { (* other character, just copy it over *)
		output_char file_name c;
		preprocess file_name lexbuf  
      }
  | eof { EOF } 

and rip_ws = parse 
  | (' ' | '\t')+ as ws { ws }
  | _  { print_string "There must be whitespace after import directive\n"; exit (-1) }

and get_file_name = parse
  | '\"'([^ '\n' '\"'])+'\"' as fn { fn }
  | _ { print_string "file name following import must be enclosed in double quotes\n"; exit (-1) }
 
{

  let lexing_store s buff max =
    let rec self n s =
      if n >= max then n
      else
        match Stream.peek s with
        | Some x ->
            Stream.junk s;
            buff.[n] <- x;
            succ n
        | _ -> n
    in
    self 0 s

  let from_context c =
    let next _ =
      let tok = with_curr_loc tokenizer c in
      let loc = Loc.of_lexbuf c.lexbuf in
      Some ((tok, loc))
    in Stream.from next

  let from_lexbuf lb =
    let c = { (default_context lb) with  loc = Loc.of_lexbuf lb}
    in from_context c

  let setup_loc lb loc =
    let start_pos = Loc.start_pos loc in
    lb.lex_abs_pos <- start_pos.pos_cnum;
    lb.lex_curr_p  <- start_pos

  let from_string loc str =
    let lb = Lexing.from_string str in
    setup_loc lb loc;
    from_lexbuf lb

  let from_stream loc strm =
    let lb = Lexing.from_function (lexing_store strm) in
    setup_loc lb loc;
    from_lexbuf lb

  let mk () loc strm = from_stream loc strm
end
}
