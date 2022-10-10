open Camlp4.PreCast

type lemma_kind_t = TLEM_TEST | TLEM_PROP | TLEM_SPLIT | TLEM_TEST_NEW | TLEM | TLEM_UNSAFE | TLEM_INFER | TLEM_INFER_PRED | TLEM_SAFE


type k_token =
  | IDENTIFIER    of string
  | INT_LITER     of int * string
  | FLOAT_LIT     of float * string
  | CHAR_LIT      of char * string
  | STRING        of string * string
        (*| COMMENT       of string*)
  | EOF 
  | JAVA          of string
  | LEMMA         of lemma_kind_t
        (*keywords*)
  | ANDLIST
  | ASSERT | ASSERT_EXACT | ASSERT_INEXACT | ASSUME | ALLN | APPEND | AXIOM
  | BIND | BOOL | BREAK | BAGMAX | BAGMIN | BAG | BARRIER 
  | PASS_COPY
  | CASE  | CAPTURERESIDUE | CLASS | COMPOSE | CONST | CONTINUE
  | CHECKSAT
  | CHECKENTAIL |  CHECKENTAIL_EXACT | CHECKENTAIL_INEXACT
  | DATA | DDEBUG | DIFF | DYNAMIC 
  | RELASSUME | RELDEFN 
  | DTIME
  | ELSE_TT
  | EMPTY
  | ENSURES | ENSURES_EXACT | ENSURES_INEXACT | ENUM | EXISTS | EXTENDS
  | FALSE | FLOAT | DBL | FORALL | FUNC
  | HTRUE
  | IF
  | IN_T | INT | INTERSECT | INV | INLINE
  | INV_EXACT | INV_SAT | BG
  | LET
  | MAX | MIN 
  | NEW | NOTIN | NULL
  | OFF | ON | ORWORD | ANDWORD
  | PRED | PRED_PRIM | DPRINT | PRED_EXT | PRINT | PRINT_LEMMAS | CMP | HIP_INCLUDE
  | PASS_REF | PASS_REF2 |REL | REQUIRES | RES of string | RETURN
  | SELFT of string | SPLIT | SUBSET | STATIC
  | THEN | THIS of string | TO | TRUE | LEXVAR
  | UNFOLD | UNION
  | VOID 
  | WHILE | FLOW of string
        (*operators*)  
  | CARET 
  | DOTDOT | ATPOS
  | ACCS | AND | ANDSTAR | ANDAND | UNIONSTAR | STARMINUS | AT | ATATSQ | ATAT | LEND | IMM | MUT | MAT | DERV | CBRACE | CLIST | COLON | COLONCOLON | COLONCOLONCOLON | COMMA | CPAREN | CSQUARE | DOLLAR
  | NI | RO
  | DOT | DOUBLEQUOTE | EQ | EQEQ | RIGHTARROW | EQUIV | GT | GTE | HASH | REL_GUARD | LEFTARROW | LENGTH
  | LT | LTE | MINUS | MEM | MEME | NEQ | NOT | NOTINLIST | OBRACE |OLIST | OPAREN | OP_ADD_ASSIGN | OP_DEC | OP_DIV_ASSIGN 
  | OP_INC | OP_MOD_ASSIGN | OP_MULT_ASSIGN | OP_SUB_ASSIGN | OR | OROR | PERM | DERIVE | EQV | CONSTR | OSQUARE  | REVERSE | SET | TAIL 
  | TOPAREN | TCPAREN
  | PERCENT | PMACRO 
  | PZERO | PFULL | PVALUE (* | PREF *)
  | PLUS | PRIME 
  | SEMICOLON | SAT | SPEC
  | STAR | DIV
  | GLOBAL |VARIANCE| ESCAPE | HPRED | REFINES | JOIN | WITH | COMBINE | FINALIZE | TRY | CATCH | FINALLY | THROWS | RAISE
  | INFER | INFER_EXACT | INFER_INEXACT | SUBANN | XPRE | PRE | XPOST | POST
  | INVLOCK 
  | LOGICAL
  | INFINITY
  | VALIDATE
  | VALID | INVALID |SSAT | SUNSAT
  | FAIL
  | FAIL_MUST
  | FAIL_MAY


module type KTokenS = Camlp4.Sig.Token with type t = k_token
  
module Token = struct
  open Format
  module Loc = Loc
  type t = k_token
  type token = t

  let sf = Printf.sprintf

  let to_string k = match k with 
    | IDENTIFIER s | INT_LITER (_,s) | FLOAT_LIT (_,s)  | CHAR_LIT (_,s) | STRING (_,s)-> s
          (*| COMMENT s -> "/* "^s^" */"*)
    | EOF -> ""
    | JAVA s-> s
    | AXIOM -> "axiom" (* [4/10/2011] An Hoa *)
    | ANDLIST -> "AndList" | ATPOS -> "at"
    | ASSERT -> "assert" | ASSERT_EXACT -> "assert_exact" | ASSERT_INEXACT -> "assert_inexact" | ASSUME -> "assume" | ALLN-> "alln" | APPEND -> "app" 
    | BIND -> "bind"| BOOL -> "bool" | BREAK ->"break" | BAGMAX ->"bagmax" | BAGMIN->"bagmin" | BAG->"bag" | BARRIER ->"barrier"
    | CASE ->"case" | CHECKENTAIL ->"checkent" | CAPTURERESIDUE ->"capture_residue" | CLASS ->"class" | CLIST -> "|]" | PASS_COPY -> "@C"
    | CHECKENTAIL_EXACT -> "checkent_exact" | CHECKENTAIL_INEXACT -> "checkent_inexact"
    | CHECKSAT -> "checksat"
    | RELASSUME -> "relAssume" | RELDEFN -> "relDefn"
    | SPEC -> "spec"
    | COMPOSE ->"compose" | CONST ->"const" | CONTINUE ->"continue"	| DATA ->"ddata" | DDEBUG ->"debug" | DIFF ->"diff"| DYNAMIC ->"dynamic"
    | DTIME ->"time" | ELSE_TT ->"else" | EMPTY -> "emp"| ENSURES ->"ensures" | ENSURES_EXACT ->"ensures_exact" | ENSURES_INEXACT ->"ensures_inexact" | ENUM ->"enum"| EXISTS ->"ex" | EXTENDS ->"extends"
    | FALSE ->"false"| FLOAT ->"float" | DBL ->"double" | FORALL ->"forall" | FUNC -> "ranking"
    | HTRUE -> "htrue"
    | IF ->"if" | IN_T ->"in_t" | INT ->"int"| INTERSECT ->"intersect" | INV->"inv" | INLINE->"inline"
    | INV_EXACT -> "inv_exact" | INV_SAT -> "inv_sat" | BG -> "BG"
    | LEMMA TLEM ->"lemma" | LEMMA TLEM_TEST ->"lemma_test" | LEMMA TLEM_TEST_NEW ->"lemma_test_new" | LEMMA TLEM_UNSAFE ->"lemma_unsafe"
    | LEMMA TLEM_SPLIT ->"lemma_split"
    | LEMMA TLEM_PROP ->"lemma_prop"
    | LEMMA TLEM_SAFE ->"lemma_safe" | LEMMA TLEM_INFER ->"lemma_infer" | LEMMA TLEM_INFER_PRED ->"lemma_infer_pred" | LET->"let" | MAX ->"max" | MIN ->"min" | NEW ->"new" | NOTIN ->"notin" | NULL ->"null"
    | OFF ->"off" | ON->"on" | ORWORD ->"or" | ANDWORD ->"and" | PRED ->"pred" | PRED_PRIM -> "pred_prim" | PRED_EXT ->"pred_extn" | HIP_INCLUDE -> "hip_include" | DPRINT ->"dprint" 
    | PRINT -> "print" 
    | PRINT_LEMMAS -> "print_lemmas" 
    |CMP -> "sleek compare" | PASS_REF ->"@R" | PASS_REF2 ->"ref"|REL->"relation" |REQUIRES ->"requires" | RES s->"res "^s 
    | RETURN->"return" | SELFT s ->"self "^s | SPLIT ->"split"| SUBSET ->"subset" | STATIC ->"static" | LEXVAR ->"LexVar"
    | THEN->"then" | THIS s->"this "^s | TO ->"to" | TRUE ->"true" | UNFOLD->"unfold" | UNION->"union"
    | VOID->"void" | WHILE ->"while" | FLOW s->"flow "^s
          (*operators*)
    | NI ->"@NI" | RO ->"@RO" | ATATSQ -> "@@[" | CARET -> "^"
    | DOTDOT ->".."
    | AND ->"&"  | ANDAND ->"&&" | ANDSTAR -> "&*" |  UNIONSTAR ->"U*" | STARMINUS -> "-*" | AT ->"@"  | ATAT -> "@@" | LEND->"@L" | ACCS ->"@A" | IMM->"@I"| DERV->"@D"| CBRACE ->"}"| COLON ->":"| COLONCOLON ->"::"| COLONCOLONCOLON -> ":::" | COMMA ->","| CPAREN->")" | CSQUARE ->"]"
    | DOLLAR ->"$" | DOT ->"." | DOUBLEQUOTE ->"\"" | DIV -> "/" | EQ ->"=" | EQEQ -> "==" | RIGHTARROW -> "<-"| EQUIV ->"<->" | GT ->">" | GTE ->">= " | HASH ->"#" | REL_GUARD -> "|#|"
    | LEFTARROW -> "->" | LT -> "<" | LTE -> "<=" | MINUS -> "-" | NEQ -> "!=" | NOT -> "!" | OBRACE ->"{" | OLIST -> "[|" | OPAREN ->"(" | OP_ADD_ASSIGN -> "+=" | OP_DEC -> "--"
    | OP_DIV_ASSIGN -> "\\=" | OP_INC -> "++" | OP_MOD_ASSIGN -> "%=" | OP_MULT_ASSIGN ->"*=" | OP_SUB_ASSIGN -> "-=" | OR -> "|" | OROR -> "||" 
    | DERIVE -> "|-" | EQV -> "-|-" | CONSTR -> "-->" |  OSQUARE -> "[" | PERCENT ->"%" | PMACRO -> "PMACRO" | PLUS -> "+" | PRIME -> "'" | SEMICOLON -> ";" | STAR -> "*"
    | RAISE -> "raise" | THROWS -> "throws" | FINALLY -> "finally" | COMBINE -> "combine" | WITH -> "with" | JOIN -> "joinpred" | REFINES -> "refines"
    | HPRED -> "ho_pred" | ESCAPE -> "escape" | VARIANCE -> "variance" | GLOBAL -> "global" | TAIL -> "tail" | SET -> "set" | REVERSE -> "reverse"
    | PERM -> "perm" | NOTINLIST -> "notinlist" | CATCH -> "catch" | TRY -> "try" | FINALIZE -> "finalizes" | LENGTH -> "len"  (* | INLIST -> "inlist"  | HEAD -> "head" *)
    | MEM -> "mem" | MEME -> "memE"
    | INFER -> "infer" | INFER_EXACT -> "infer_exact" | INFER_INEXACT -> "infer_inexact"
    | PRE -> "@pre" | XPRE -> "@xpre" | MUT -> "@M" | MAT -> "@R" | POST -> "@post" | XPOST -> "@xpost" | SUBANN -> "<:" | SAT -> "@S"
          (* | PREF -> "@p_ref" *) | PVALUE -> "@value" | PFULL -> "@full" | PZERO -> "@zero"
    | INVLOCK->"inv_lock"
    | LOGICAL -> "logical"
    | INFINITY -> "\\inf"
    | VALIDATE -> "expect"
    | VALID -> "valid"
    | INVALID -> "invalid"
    | SSAT -> "sat"
    | SUNSAT -> "unsat"
    | FAIL -> "Fail"
    | FAIL_MUST -> "Fail_Must"
    | FAIL_MAY -> "Fail_May"
    | TOPAREN -> "<#" 
    | TCPAREN -> "#>" (*Open and close paren for thread heap*)


  let print ppf x = pp_print_string ppf (to_string x)

  let match_keyword kwd _ = false 
    
  let extract_string t = match t with
     | IDENTIFIER s | INT_LITER (_,s) | FLOAT_LIT (_,s)  | CHAR_LIT (_,s) | STRING (_,s) (*| COMMENT s*) | JAVA s | RES s | SELFT s | THIS s | FLOW s -> s
     | _ -> ""
     
    
  module Error = struct
    type t = string
    exception E of string
    let print = pp_print_string
    let to_string x = x
  end

  module Filter = struct
    type token_filter = (t, Loc.t) Camlp4.Sig.stream_filter

    type t =
      { is_kwd : string -> bool;
        mutable filter : token_filter }

    let mk is_kwd =
      { is_kwd = is_kwd;
        filter = (fun s -> s) }

    let filter x = fun strm -> x.filter strm

    let define_filter x f = x.filter <- f x.filter

    let keyword_added _ _ _ = ()
    let keyword_removed _ _ = ()
  end

end
module Error = Camlp4.Struct.EmptyError
