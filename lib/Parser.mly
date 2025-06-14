%token EOF

%token<string> ID
%token<int>    INT
%token<float>  FLOAT
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

%token<string> P_OP_AND    "&&"
%token<string> P_OP_OR     "||"
%token<string> P_OP_POW    "**"
%token<string> P_OP_MUL    "*"
%token<string> P_OP_ADD    "+"
%token<string> P_OP_CONCAT "^"
%token<string> P_OP_CMP    "<"

%token KW_AND      "and"
%token KW_ELSE     "else"
%token KW_EXTERNAL "external"
%token KW_FALSE    "false"
%token KW_FUN      "fun"
%token KW_IF       "if"
%token KW_IN       "in"
%token KW_INCLUDE  "include"
%token KW_LET      "let"
%token KW_LOCAL    "local"
%token KW_OPEN     "open"
%token KW_THEN     "then"
%token KW_TRUE     "true"
%token KW_TYPE     "type"
%token KW_UNWRAP   "unwrap"
%token KW_WITH     "with"
%token KW_WRAP     "wrap"

%right "->" "=>"
%left ":>" ":" "with"
%left LET

%left  "<"
%right "||"
%right "&&"
%right "^"
%left  "+"
%left  "*"
%right "**"


%start<Surface.Ast.bind list> file
%start<Surface.Ast.expr> repl

%{
  open Surface
  open Surface.Node
  open Surface.Ast

  module OneMl = struct end (* https://github.com/ocaml/dune/issues/2450#issuecomment-515895672 *)

  let ( @@ ) data span = { data; span = Some span }
  let ( @? ) data span = { data; span }
%}

%type<Surface.Ast.typ> typ
%type<Surface.Ast.decl> decl
%type<Surface.Ast.expr> expr
%type<Surface.Ast.bind> bind
%type<Surface.Ast.ident> ident

%%

file:
  | es=punctuated_list(";"+, bind) EOF { es }
;

repl:
  | e=expr EOF { e }
;

typ:
  | t=typ_app { t }
  | "(" x=ident ":" t1=typ ")" "=>" t2=typ %prec P_ARROW { TArrow (x, t1, Pure,   t2) @@ $loc }
  | "(" x=ident ":" t1=typ ")" "->" t2=typ %prec P_ARROW { TArrow (x, t1, Impure, t2) @@ $loc }

  | "wrap" t=typ { TWrapped t @@ $loc }

  (* Sugar *)
  | t1=typ "->" t2=typ { TArrow (Ident.fresh () @@ $loc(t1), t1, Impure, t2) @@ $loc }
  | t1=typ "=>" t2=typ { TArrow (Ident.fresh () @@ $loc(t1), t1, Pure,   t2) @@ $loc }

  | t=typ "with" ps=separated_nonempty_list("and", param_with) { Sugar.typ_with ~span:$loc t ps }
;

param_with:
  | "type" xs=separated_nonempty_list(".", ident) ps=param* "=" t=typ_app { xs, ps, TSingleton (EType t @? t.span) @? t.span }
  |        xs=separated_nonempty_list(".", ident) ps=param* "=" e=expr_op { xs, ps, TSingleton e @? e.span }
  |        xs=separated_nonempty_list(".", ident) ps=param* ":" t=typ_app { xs, ps, t }
;

typ_app:
  | t=typ_atom       { t }
  | t=typ_path       { TExpr t @@ $loc }
  | "(" t=typ ")"    { t }
;

typ_path:
  | t=typ_path_atom ts=typ_path_arg* { Sugar.expr_app ~span:$loc t ts }
;

typ_path_arg:
  | t=typ_path_atom    { t }
  | t=typ_atom         { EType t @@ $loc }
  | "(" t=typ_path ")" { t }

  | "(" "wrap" t=typ ")"     { EType (TWrapped t @@ $loc) @@ $loc }
;

typ_path_atom:
  | id=ident                     { EVar id @@ $loc }
  | t=typ_path_atom "." id=ident { EProj (t, id) @@ $loc }
;

typ_atom:
  | "type"              { TType @@ $loc }
  | "(" "=" e=expr ")"  { TSingleton e @@ $loc }
  | "external" x=STRING { Sugar.typ_external ~span:$loc x }

  | "{" ds=punctuated_list(";"+, decl) "}" { TStruct ds @@ $loc }
;

decl:
  | "include" t=typ { DIncl t @@ $loc }
  | "open"    t=typ { DOpen t @@ $loc }

  (* Sugar *)
  | id=ident ps=param* ":" t=typ        { Sugar.decl_id     ~span:$loc id ps t }
  | id=ident ps=param* "=" e=expr       { Sugar.decl_id_eq  ~span:$loc id ps e }
  | "type" id=ident ps=param*           { Sugar.decl_typ    ~span:$loc id ps }
  | "type" id=ident ps=param* "=" t=typ { Sugar.decl_typ_eq ~span:$loc id ps t }
;

expr:
  | e=expr_op         { e }

  | "fun" ps=param+ "=>" e=expr { Sugar.expr_fun ~span:$loc ps e }

  (* Sugar *)
  | "let" b=punctuated_list("and", bind) "in" e=expr %prec LET { Sugar.expr_let_in ~span:$loc b e }
  | e=expr ":>" t=typ_app                                     { Sugar.expr_seal   ~span:$loc e t }
  | e=expr ":"  t=typ_app                                     { Sugar.expr_annot  ~span:$loc e t }
;

expr_op:
  | e=expr_app { e }

  | "if" c=expr "then" e1=expr "else" e2=expr_op ":" t=typ_app { Sugar.expr_cond ~span:$loc c e1 e2 t }

  | "wrap"   e=expr_op ":" t=typ_app { Sugar.expr_wrap   ~span:$loc e t }
  | "unwrap" e=expr_op ":" t=typ_app { Sugar.expr_unwrap ~span:$loc e t }

  | lhs=expr_op op=op("||") rhs=expr_op { Sugar.expr_op ~span:$loc op lhs rhs }
  | lhs=expr_op op=op("&&") rhs=expr_op { Sugar.expr_op ~span:$loc op lhs rhs }
  | lhs=expr_op op=op("<")  rhs=expr_op { Sugar.expr_op ~span:$loc op lhs rhs }
  | lhs=expr_op op=op("^")  rhs=expr_op { Sugar.expr_op ~span:$loc op lhs rhs }
  | lhs=expr_op op=op("+")  rhs=expr_op { Sugar.expr_op ~span:$loc op lhs rhs }
  | lhs=expr_op op=op("*")  rhs=expr_op { Sugar.expr_op ~span:$loc op lhs rhs }
  | lhs=expr_op op=op("**") rhs=expr_op { Sugar.expr_op ~span:$loc op lhs rhs }
;

%inline
op(X):
  | x=X { EVar (Ident.named x @@ $loc) @@ $loc }
;

expr_app:
  | e=expr_atom es=expr_atom* { Sugar.expr_app ~span:$loc e es }
  | "type" t=typ_app          { EType t @@ $loc }
;

expr_atom:
  | id=ident       { EVar id @@ $loc }
  | "(" ")"        { EConst (Prim.ConstUnit ()) @@ $loc }
  | "true"         { EConst (Prim.ConstBool true) @@ $loc }
  | "false"        { EConst (Prim.ConstBool false) @@ $loc }
  | x=INT          { EConst (Prim.ConstInt x) @@ $loc }
  | x=FLOAT        { EConst (Prim.ConstFloat x) @@ $loc }
  | x=STRING       { EConst (Prim.ConstString x) @@ $loc }
  | "(" e=expr ")" { e }

  | e=expr_atom "." id=ident               { EProj (e, id) @@ $loc }
  | "{" bs=punctuated_list(";"+, bind) "}" { EStruct bs @@ $loc }
;

bind:
  | "include" e=expr { BIncl e @@ $loc }
  | "open"    e=expr { BOpen e @@ $loc }

  (* Sugar *)
  | id=ident ps=param* ts1=preceded(":", typ)* ts2=preceded(":>", typ)* "=" e=expr
    { Sugar.bind_id ~span:$loc id ps ts1 ts2 e }

  | "type" id=ident ps=param* "=" t=typ
    { Sugar.bind_typ ~span:$loc id ps t }

  | "external" id=ident ":" t=typ "=" sym=STRING
    { BVal (id, EExternal (sym, t) @@ $loc) @@ $loc }
;

param:
  |     id=ident               { id, TType @@ $loc }
  | "(" id=ident ":" t=typ ")" { id, t }
;


ident:
  | id=ID                  { Ident.named id @@ $loc }
  | "(" id=P_OP_POW    ")" { Ident.named id @@ $loc }
  | "(" id=P_OP_MUL    ")" { Ident.named id @@ $loc }
  | "(" id=P_OP_ADD    ")" { Ident.named id @@ $loc }
  | "(" id=P_OP_CONCAT ")" { Ident.named id @@ $loc }
  | "(" id=P_OP_CMP    ")" { Ident.named id @@ $loc }
;

(* Possibly empty list of X separated by sep, with optional trailing separator when non-empty. *)
punctuated_list(sep, X):
  |                                    { [] }
  | x=X                                { [x] }
  | x=X sep xs=punctuated_list(sep, X) { x :: xs }
;
