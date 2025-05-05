%token<string> IDENT
%token<int> INT
%token<string> STRING

%token KW_UNIT     "unit"
%token KW_BOOL     "bool"
%token KW_INT      "int"
%token KW_STRING   "string"

%token KW_TRUE     "true"
%token KW_FALSE    "false"

%token KW_AS       "as"
%token KW_EXISTS   "exists"
%token KW_EXTERNAL "external"
%token KW_FORALL   "forall"
%token KW_IN       "in"
%token KW_LAMBDA   "lambda"
%token KW_LET      "let"
%token KW_PACK     "pack"
%token KW_UNPACK   "unpack"

%token P_ARROW     "->"
%token P_BRACE_L   "{"
%token P_BRACE_R   "}"
%token P_BRACKET_L "["
%token P_BRACKET_R "]"
%token P_COMMA     ","
%token P_COLON     ":"
%token P_DOT       "."
%token P_EQ        "="
%token P_PAREN_L   "("
%token P_PAREN_R   ")"
%token P_STAR      "*"
%token P_SEMI      ";"

%right "->"

%token EOF

%start<One_ml.FOmega.term list> program

%start<One_ml.FOmega.typ>  toptyp
%start<One_ml.FOmega.term> topexpr

%{
  open One_ml.FOmega

  let env = [], []

  let add_var x (vars, typs) = (x :: vars, typs)
  let add_typ x (vars, typs) = (vars, x :: typs)

  let find_var x (vars, _) = match List.find_index ((=) x) vars with
    | None -> Error.undefined_variable x
    | Some i -> i
  ;;

  let find_typ x (_, typs) = match List.find_index ((=) x) typs with
    | None -> Error.undefined_variable x
    | Some i -> i
  ;;

  let desugar_typ_param_list f t xs env =
    let rec aux env = function
      | [] -> t env
      | (b, k) :: xs -> f b k (aux (add_typ b env) xs)
    in
    aux env xs
  ;;

  let desugar_var_param_list e xs env =
    let rec aux env = function
      | [] -> e env
      | (b, Either.Left t) :: xs -> TmLam (b, t env, aux (add_var b env) xs)
      | (b, Either.Right k) :: xs -> TmTyLam (b, k, aux (add_typ b env) xs)
    in
    aux env xs
  ;;

  let desugar_let_binding b t e1 e2 env = TmApp (TmLam (b, t env, e2 (add_var b env)), e1 env)
%}

%%

program: es=punctuated_list(";"+, expr) EOF { List.map (fun e -> e env) es }

toptyp:  t=typ  EOF { t env };
topexpr: e=expr EOF { e env };

label:
  | l=IDENT { l }
  | l=INT   { string_of_int l }
;

kind:
  | "*"                  { KStar }
  | k1=kind "->" k2=kind { KArrow (k1, k2) }
  | "(" k=kind ")"       { k }
;

typ:
  | t=typ_fun { t }
  | "forall" ts=typ_param_list "." t=typ { desugar_typ_param_list (fun b k t -> TyForall (b, k, t)) t ts }
  | "exists" ts=typ_param_list "." t=typ { desugar_typ_param_list (fun b k t -> TyExists (b, k, t)) t ts }
  | "lambda" ts=typ_param_list "." t=typ { desugar_typ_param_list (fun b k t -> TyLam (b, k, t)) t ts }
;

%inline
typ_param_list:
  | ts=separated_nonempty_list(",", typ_param) { ts }
;

typ_param:
  | b=IDENT ":" k=kind { b, k }
  | b=IDENT            { b, KStar }
;

typ_fun:
  | t=typ_app { t }
  | lhs=typ_fun "->" rhs=typ_fun { fun env -> TyArrow (lhs env, rhs env) }
;

typ_app:
  | t=typ_atom { t }
  | lhs=typ_app rhs=typ_atom { fun env -> TyApp (lhs env, rhs env) }
;

typ_atom:
  | "(" t=typ ")" { t }

  | id=IDENT { fun env -> TyVar (find_typ id env) }
  | "unit"   { Fun.const (TyPrim PrimUnit) }
  | "bool"   { Fun.const (TyPrim PrimBool) }
  | "int"    { Fun.const (TyPrim PrimInt) }
  | "string" { Fun.const (TyPrim PrimString) }

  | "{" ts=typ_record_field_list "}" { fun env -> TyRecord (ts env) }
;

%inline typ_record_field_list:
  | ts=punctuated_list(",", l=label ":" t=typ { l, t })
    { fun env -> List.map (fun (l, t) -> l, t env) ts }
;

expr:
  | e=expr_app { e }
  | "lambda" es=expr_param_list "." e=expr { desugar_var_param_list e es }

  | "pack" e=expr "as" "exists" b=IDENT ":" k=kind "=" t1=typ "." t2=typ { fun env -> TmPack (t1 env, e env, b, k,     t2 (add_typ b env)) }
  | "pack" e=expr "as" "exists" b=IDENT            "=" t1=typ "." t2=typ { fun env -> TmPack (t1 env, e env, b, KStar, t2 (add_typ b env)) }

  | "unpack" b1=IDENT "," b2=IDENT "=" e1=expr "in" e2=expr { fun env -> TmUnpack (b1, b2, e1 env, e2 (env |> add_typ b1 |> add_var b2)) }

  | "let"  b=IDENT ":" t=typ  "=" e1=expr "in" e2=expr { desugar_let_binding b t e1 e2 }
;

%inline
expr_param_list:
  | es=separated_nonempty_list(",", expr_param) { es }
;

expr_param:
  | x=IDENT ":" t=typ          { x, Either.Left t }
  | "[" x=IDENT ":" k=kind "]" { x, Either.Right k }
  | "[" x=IDENT "]"            { x, Either.Right KStar }
;

expr_app:
  | e=expr_atom { e }
  | lhs=expr_app rhs=expr_atom   { fun env -> TmApp   (lhs env, rhs env) }
  | lhs=expr_app "[" rhs=typ "]" { fun env -> TmTyApp (lhs env, rhs env) }
;

expr_atom:
  | "(" e=expr ")" { e }

  | id=IDENT { fun env -> TmVar (find_var id env) }
  | "(" ")"  { Fun.const (TmPrim (ConstUnit ())) }
  | "true"   { Fun.const (TmPrim (ConstBool true)) }
  | "false"  { Fun.const (TmPrim (ConstBool false)) }
  | x=INT    { Fun.const (TmPrim (ConstInt x)) }
  | s=STRING { Fun.const (TmPrim (ConstString s)) }

  | x=expr_atom "." l=label { fun env -> TmProj (x env, l) }
  | "external" id=IDENT     { Fun.const (TmExternal id) }

  | "{" es=expr_record_field_list "}" { fun env -> TmRecord (es env) }
;

%inline expr_record_field_list:
  | es=punctuated_list(",", l=label "=" e=expr { l, e })
    { fun env -> List.map (fun (l, e) -> l, e env) es }
;

punctuated_list(sep, X):
  |                                    { [] }
  | x=X                                { [x] }
  | x=X sep xs=punctuated_list(sep, X) { x :: xs }
;
