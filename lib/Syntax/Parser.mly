%token EOF

%token<string> ID
%token<int>    INT
%token<float>  FLOAT
%token<char>   CHAR
%token<string> STRING

%token P_ARROW     "->"
%token P_ARROW_FAT "=>"
%token P_BRACE_L   "{"
%token P_BRACE_R   "}"
%token P_COLON     ":"
%token P_COMMA     ","
%token P_DOT       "."
%token P_EQUAL     "="
%token P_PAREN_L   "("
%token P_PAREN_R   ")"
%token P_SEAL      ":>"
%token P_SEMI      ";"
%token P_TICK      "'"
%token P_UNDER     "_"

%token<string> P_OP_AND    "&&"
%token<string> P_OP_OR     "||"
%token<string> P_OP_POW    "**"
%token<string> P_OP_MUL    "*"
%token<string> P_OP_ADD    "+"
%token<string> P_OP_CONCAT "^"
%token<string> P_OP_CMP    "<"

%token KW_AND      "and"
%token KW_DO       "do"
%token KW_ELSE     "else"
%token KW_EXTERN   "extern"
%token KW_FUN      "fun"
%token KW_IF       "if"
%token KW_IN       "in"
%token KW_INCLUDE  "include"
%token KW_LET      "let"
%token KW_OPEN     "open"
%token KW_THEN     "then"
%token KW_TYPE     "type"
%token KW_UNWRAP   "unwrap"
%token KW_WITH     "with"
%token KW_WRAP     "wrap"

%right "->" "=>"
%left "else"
%left "let"
%left ":>" ":" "with"

%right "||"
%right "&&"
%left  "<"
%right "^"
%left  "+"
%left  "*"
%right "**"

%start<Lang.Surface.file> file
%start<(Lang.Surface.expr, Lang.Surface.file) Either.t> repl_line

%{
  open Lang.Surface
  open Lang.Common

  module OneMl = struct end (* https://github.com/ocaml/dune/issues/2450#issuecomment-515895672 *)

  let ( @@ ) node span = Node.make ~span node
%}

%%

file:
  | bs=punctuated_list(";"+, bind) EOF { List.concat bs }
;

repl_line:
  | e=expr EOF                        { Either.Left e }
  | bs=punctuated_list(";"+, bind) EOF { Either.Right (List.concat bs) }
;

(* Types *)

typ:
  | t=typ_app { t }

  | "(" x=var ":" t1=typ ")" "=>" t2=typ %prec P_ARROW { Sugar.T (TArrow (x, Sugar.as_typ t1, Explicit, Pure,   Sugar.as_typ t2) @@ $loc) }
  | "(" x=var ":" t1=typ ")" "->" t2=typ %prec P_ARROW { Sugar.T (TArrow (x, Sugar.as_typ t1, Explicit, Impure, Sugar.as_typ t2) @@ $loc) }

  | "wrap" t=typ_atom { Sugar.T (TWrapped (Sugar.as_typ t) @@ $loc) }

  (* Sugar *)
  | t1=typ "=>" t2=typ %prec P_ARROW { Sugar.T (TArrow (Sugar.ident (Some $loc(t1)), Sugar.as_typ t1, Explicit, Pure,   Sugar.as_typ t2) @@ $loc) }
  | t1=typ "->" t2=typ %prec P_ARROW { Sugar.T (TArrow (Sugar.ident (Some $loc(t1)), Sugar.as_typ t1, Explicit, Impure, Sugar.as_typ t2) @@ $loc) }

  | "'" "(" x=var ":" t="type" ")" "=>" t2=typ %prec P_ARROW { Sugar.T (TArrow (x, TType @@ $loc(t), Implicit, Pure, Sugar.as_typ t2) @@ $loc) }
  | "'"     x=var                  "=>" t2=typ %prec P_ARROW { Sugar.T (TArrow (x, TType @@ $loc(x), Implicit, Pure, Sugar.as_typ t2) @@ $loc) }

  | t=typ "with" ps=separated_nonempty_list("and", with_param)
    { Sugar.T (Sugar.typ_with ~span:$loc (Sugar.as_typ t) ps) }
;

typ_app:
  | t=typ_atom              { t }
  | t=typ_proj ts=typ_atom+ { Sugar.E (Sugar.typ_app ~span:$loc t (List.map Sugar.as_expr ts)) }
;

typ_atom:
  | "type"                   { Sugar.T (TType @@ $loc) }
  | "_"                      { Sugar.T (THole @@ $loc) }
  | "(" ")"                  { Sugar.T (TPrim PUnit @@ $loc) }
  | "(" "=" "type" t=typ ")" { Sugar.T (TSingletonType (Sugar.as_typ t) @@ $loc) }
  | "extern" x=STRING        { Sugar.T (Sugar.typ_extern ~span:$loc x) }
  | "(" t=typ ")"            { t }

  | t=typ_proj { Sugar.E t }

  | "{" ds=punctuated_list(";"+, decl) "}"        { Sugar.T (TStruct ds @@ $loc) }
  | "(" ts=punctuated_nonempty_list(",", typ) ")" { Sugar.T (Sugar.typ_tuple ~span:$loc (List.map Sugar.as_typ ts)) }
;

typ_proj:
  | x=var                 { EVar x @@ $loc }
  | t=typ_proj "." x=proj { EProj (t, x) @@ $loc }
;

decl:
  | "include" t=typ { DIncl (Public,  Sugar.as_typ t) @@ $loc }
  | "open"    t=typ { DIncl (Private, Sugar.as_typ t) @@ $loc }

  (* Sugar *)
  | x=var ps=param* ":" t=typ            { Sugar.decl_id     ~span:$loc x ps (Sugar.as_typ t) }
  | x=var ps=param* "=" "type" t=typ     { Sugar.decl_typ_eq ~span:$loc x ps (Sugar.as_typ t) }
  | "type" x=var ps=typ_param*           { Sugar.decl_typ    ~span:$loc x ps }
  | "type" x=var ps=typ_param* "=" t=typ { Sugar.decl_typ_eq ~span:$loc x ps (Sugar.as_typ t) }
;

with_param:
  | "type" xs=separated_nonempty_list(".", proj) ps=typ_param* "="    t=typ_app { xs, ps, Sugar.typ_singleton ~span:$loc(t) (Sugar.as_typ t) }
  |        xs=separated_nonempty_list(".", proj) ps=param* "=" "type" t=typ_app { xs, ps, Sugar.typ_singleton ~span:$loc(t) (Sugar.as_typ t) }
  |        xs=separated_nonempty_list(".", proj) ps=param* ":"        t=typ_app { xs, ps, Sugar.as_typ t }
;

%inline
toption(X):
  |     { Sugar.T (THole @@ $loc) }
  | x=X { x }
;

(* Expressions *)

expr:
  | e=expr_op         { e }

  | "fun" ps=param+ "=>" e=expr { Sugar.expr_fun ~span:$loc ps e }

  (* Sugar *)
  | "let" bs=separated_nonempty_list("and", bind) "in" e=expr %prec KW_LET
    { Sugar.expr_let_in ~span:$loc (List.concat bs) e }

  | e=expr ":>" t=typ { Sugar.expr_seal   ~span:$loc e (Sugar.as_typ t) }
  | e=expr ":"  t=typ { Sugar.expr_annot  ~span:$loc e (Sugar.as_typ t) }
;

expr_op:
  | e=expr_app { e }

  | "if" c=expr "then" e1=expr "else" e2=expr_op t=toption(preceded(":", typ))
    { Sugar.expr_cond ~span:$loc c e1 e2 (Sugar.as_typ t) }

  | "wrap"   e=expr_op ":" t=typ { Sugar.expr_wrap   ~span:$loc e (Sugar.as_typ t) }
  | "unwrap" e=expr_op ":" t=typ { Sugar.expr_unwrap ~span:$loc e (Sugar.as_typ t) }

  | "extern" sym=STRING ":" t=typ { EExtern (sym, Sugar.as_typ t) @@ $loc }

  | lhs=expr_op op="||" rhs=expr_op { Sugar.expr_or  ~span:$loc ~op:$loc(op) lhs rhs }
  | lhs=expr_op op="&&" rhs=expr_op { Sugar.expr_and ~span:$loc ~op:$loc(op) lhs rhs }

  | lhs=expr_op op=op rhs=expr_op { Sugar.expr_op ~span:$loc ~op:$loc(op) op lhs rhs }
;

expr_app:
  | e=expr_atom es=expr_atom* { Sugar.expr_app ~span:$loc e es }
  | "type" t=typ              { EType (Sugar.as_typ t) @@ $loc }
;

expr_atom:
  | x=var          { EVar x @@ $loc }
  | "(" ")"        { EConst (Const.CUnit ()) @@ $loc }
  | x=INT          { EConst (Const.CInt x) @@ $loc }
  | x=FLOAT        { EConst (Const.CFloat x) @@ $loc }
  | x=CHAR         { EConst (Const.CChar x) @@ $loc }
  | x=STRING       { EConst (Const.CString x) @@ $loc }
  | "(" e=expr ")" { e }

  | e=expr_atom "." x=proj { EProj (e, x) @@ $loc }

  | "{" bs=punctuated_list(";"+, bind) "}"         { EStruct (List.concat bs) @@ $loc }
  | "(" es=punctuated_nonempty_list(",", expr) ")" { Sugar.expr_tuple ~span:$loc es }
;

bind:
  | "include" e=expr { [BIncl (Public,  e) @@ $loc] }
  | "open"    e=expr { [BIncl (Private, e) @@ $loc] }

  (* Sugar *)
  | p=pat "=" e=expr { Sugar.bind_pat ~span:$loc p e }
  | x=var            { Sugar.bind_pat ~span:$loc (Sugar.PId x @@ $loc(x)) (EVar x @@ $loc(x)) }

  | x=var ps=param+ rs=bind_fun_annot* "=" e=expr
    { [ Sugar.bind_fun ~span:$loc x ps rs e ] }

  | "type" x=var ps=typ_param* "=" t=typ { Sugar.bind_typ ~span:$loc x ps (Sugar.as_typ t) }
  | "do"   e=expr                        { Sugar.bind_do  ~span:$loc e }
;

bind_fun_annot:
  | ":"  t=typ { fun e -> Sugar.expr_annot ~span:$loc e (Sugar.as_typ t) }
  | ":>" t=typ { fun e -> Sugar.expr_seal  ~span:$loc e (Sugar.as_typ t) }
;

param:
  | p=pat_atom  { p, Explicit }

  | "'"     x=var                { Sugar.pat_typ ~span:$loc(x) x, Implicit }
  | "'" "(" x=var ":" "type" ")" { Sugar.pat_typ ~span:$loc(x) x, Implicit }
;

typ_param:
  |     x=var                { Sugar.pat_typ ~span:$loc(x) x,                                 Explicit }
  | "(" x=var ":" t=typ ")"  { Sugar.PAnnot (Sugar.PId x @@ $loc(x), Sugar.as_typ t) @@ $loc, Explicit }

  | "'"     x=var                { Sugar.pat_typ ~span:$loc(x) x, Implicit }
  | "'" "(" x=var ":" "type" ")" { Sugar.pat_typ ~span:$loc(x) x, Implicit }

pat:
  | p=pat_atom                   { p }

  |        p=pat      ":"  t=typ { Sugar.PAnnot (p, Sugar.as_typ t) @@ $loc }
  |        p=pat      ":>" t=typ { Sugar.PSeal  (p, Sugar.as_typ t) @@ $loc }
  | "wrap" p=pat_atom ":"  t=typ { Sugar.PWrap  (p, Sugar.as_typ t) @@ $loc }
;

pat_atom:
  | x=var         { Sugar.PId x @@ $loc }
  | "_"           { Sugar.PHole @@ $loc }
  | "(" p=pat ")" { p }

  | "{" ps=punctuated_list(";"+, pat_bind) "}"    { Sugar.PStruct ps @@ $loc }
  | "(" ps=punctuated_nonempty_list(",", pat) ")" { Sugar.pat_tuple ~span:$loc ps }

pat_bind:
  | x=var "=" p=pat { x, p }
  | x=var           { x, Sugar.PId x @@ $loc }
;

(* Atoms *)

var:
  | id=ID         { id @@ $loc }
  | "(" id=op ")" { id @@ $loc }
;

proj:
  | id=ID  { id @@ $loc }
  | id=op  { id @@ $loc }
  | id=INT { Int.to_string id @@ $loc }
;

%inline
op:
  | id=P_OP_POW    { id }
  | id=P_OP_MUL    { id }
  | id=P_OP_ADD    { id }
  | id=P_OP_CONCAT { id }
  | id=P_OP_CMP    { id }
;

(* Utilities *)

(* Possibly empty list of X separated by sep, with optional trailing separator when non-empty. *)
punctuated_list(sep, X):
  |                                    { [] }
  | x=X                                { [x] }
  | x=X sep xs=punctuated_list(sep, X) { x :: xs }
;

(* Non-empty list of X separated by sep, with required (when length is 1) or optional (otherwise) trailing separator. *)
punctuated_nonempty_list(sep, X):
  | x=X sep xs=punctuated_list(sep, X) { x :: xs }
;
