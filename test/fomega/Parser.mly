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

%start<OneMl.FOmega.Expr.t list> program
%start<OneMl.FOmega.Expr.t> repl

%{
  open OneMl
  open OneMl.FOmega
  open OneMl.FOmega.Kind
  open OneMl.FOmega.Type
  open OneMl.FOmega.Expr

  type exkind = KEx:  'k Kind.t -> exkind
  type extvar = TVEx: 'k TVar.t -> extvar
  type extyp  = TEx:  'k Type.t -> extyp

  type env =
  { vars: (string * Var.t) list
  ; typs: (string * extvar) list
  }

  let env = { vars = []; typs = [] }

  let add_var name env =
    let x = Var.fresh ~name () in
    x, { env with vars = (name, x) :: env.vars }
  ;;

  let add_typ name kind env =
    let x = TVar.fresh ~name kind in
    x, { env with typs = (name, TVEx x) :: env.typs }
  ;;

  let find_var x env = match List.assoc_opt x env.vars with
    | None -> Printf.ksprintf failwith "Unbound variable `%s'" x
    | Some x -> EVar x
  ;;

  let find_typ x env = match List.assoc_opt x env.typs with
    | None -> Printf.ksprintf failwith "Unbound variable `%s'" x
    | Some (TVEx x) -> TEx (TVar x)
  ;;

  let ttyp t: Kind.ktyp Type.t =
    let TEx t = t in
    match Kind.hequal (Type.kind t) KType with
      | Some Util.Equal -> t
      | None -> failwith "Expected type kind"
  ;;

  let tapp t1 t2 =
    let TEx t1, TEx t2 = t1, t2 in
    match Type.kind t1, Type.kind t2 with
      | KArrow (k1, _), k1' -> (match Kind.hequal k1 k1' with
          | Some Util.Equal -> TEx (TApp (t1, t2))
          | None -> failwith "Type application kind mismatch")
      | _, _ -> failwith "Expected arrow kind"
  ;;

  let desugar_typ_param_list f t xs env =
    let rec aux env = function
      | [] -> t env
      | (x, KEx k) :: xs ->
        let x, env = add_typ x k env in
        f (TVEx x) (aux env xs)
    in
    aux env xs
  ;;

  let desugar_var_param_list e xs env =
    let rec aux env = function
      | [] -> e env
      | (x, Either.Left t) :: xs ->
        let x, env' = add_var x env in
        ELam (x, ttyp (t env), aux env' xs)
      | (x, Either.Right (KEx k)) :: xs ->
        let x, env' = add_typ x k env in
        ETyLam (x, aux env' xs)
    in
    aux env xs
  ;;

  let desugar_let_binding x t e1 e2 env =
    let x, env' = add_var x env in
    EApp (ELam (x, ttyp (t env), e2 env'), e1 env)
  ;;
%}

%%

program: es=punctuated_list(";"+, expr) EOF { List.map (fun e -> e env) es }

repl: e=expr EOF { e env }

label:
  | l=IDENT { l }
  | l=INT   { string_of_int l }
;

kind:
  | "*"                  { KEx KType }
  | k1=kind "->" k2=kind { let KEx k1, KEx k2 = k1, k2 in KEx (KArrow (k1, k2)) }
  | "(" k=kind ")"       { k }
;

kind_annot:
  |            { KEx KType }
  | ":" k=kind { k }
;

typ:
  | t=typ_fun { t }
  | "forall" ts=typ_param_list "." t=typ { desugar_typ_param_list (fun (TVEx x) t -> TEx (TForall (x, ttyp t))) t ts }
  | "exists" ts=typ_param_list "." t=typ { desugar_typ_param_list (fun (TVEx x) t -> TEx (TExists (x, ttyp t))) t ts }
  | "lambda" ts=typ_param_list "." t=typ { desugar_typ_param_list (fun (TVEx x) (TEx t) -> TEx (TLam (x, t))) t ts }
;

typ_annot:
  | ":" t=typ { t }
;

%inline
typ_param_list:
  | ts=separated_nonempty_list(",", typ_param) { ts }
;

typ_param:
  | x=IDENT k=kind_annot { x, k }
;

typ_fun:
  | t=typ_app { t }
  | lhs=typ_fun "->" rhs=typ_fun { fun env -> TEx (TArrow (ttyp (lhs env), ttyp (rhs env))) }
;

typ_app:
  | t=typ_atom { t }
  | lhs=typ_app rhs=typ_atom { fun env -> tapp (lhs env) (rhs env) }
;

typ_atom:
  | "(" t=typ ")" { t }

  | id=IDENT { find_typ id }
  | "unit"   { Fun.const (TEx (TPrim PrimUnit)) }
  | "bool"   { Fun.const (TEx (TPrim PrimBool)) }
  | "int"    { Fun.const (TEx (TPrim PrimInt)) }
  | "string" { Fun.const (TEx (TPrim PrimString)) }

  | "{" ts=typ_record_field_list "}" { fun env -> TEx (TRecord (ts env)) }
;

%inline typ_record_field_list:
  | ts=punctuated_list(",", l=label ":" t=typ { l, t })
    { fun env -> List.map (fun (l, t) -> l, ttyp (t env)) ts }
;

expr:
  | e=expr_app { e }
  | "lambda" es=expr_param_list "." e=expr { desugar_var_param_list e es }

  | "pack" t=typ "," e=expr "as" s=typ { fun env ->
      let TEx t = t env in
      EPack (t, e env, ttyp (s env))
    }

  | "unpack" a=IDENT k=kind_annot "," x=IDENT "=" e1=expr "in" e2=expr { fun env ->
      let KEx k = k in
      let a, env' = add_typ a k env in
      let x, env' = add_var x env' in
      EUnpack (a, x, e1 env, e2 env')
    }

  | "let" x=IDENT t=typ_annot "=" e1=expr "in" e2=expr { desugar_let_binding x t e1 e2 }
;

%inline
expr_param_list:
  | es=separated_nonempty_list(",", expr_param) { es }
;

expr_param:
  |     b=IDENT t=typ_annot      { b, Either.Left t }
  | "[" b=IDENT k=kind_annot "]" { b, Either.Right k }
;

expr_app:
  | e=expr_atom { e }
  | lhs=expr_app rhs=expr_atom   { fun env -> EApp  (lhs env, rhs env) }
  | lhs=expr_app "[" rhs=typ "]" { fun env -> let TEx t = rhs env in ETyApp (lhs env, t) }
;

expr_atom:
  | "(" e=expr ")" { e }

  | id=IDENT { find_var id }
  | "(" ")"  { Fun.const (EPrim (ConstUnit ())) }
  | "true"   { Fun.const (EPrim (ConstBool true)) }
  | "false"  { Fun.const (EPrim (ConstBool false)) }
  | x=INT    { Fun.const (EPrim (ConstInt x)) }
  | s=STRING { Fun.const (EPrim (ConstString s)) }

  | x=expr_atom "." l=label               { fun env -> EProj (x env, l) }
  | "(" "external" id=IDENT ":" t=typ ")" { fun env -> EExternal (id, ttyp (t env)) }
  | "{" es=expr_record_field_list "}"     { fun env -> ERecord (es env) }
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
