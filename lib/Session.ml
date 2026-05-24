open Util
module S = Lang.Surface
module T = Lang.Typed
module F = Lang.FOmega

module Sources : sig
  type t

  val create : unit -> t
  val add : t -> string -> string -> unit
  val find : t -> string -> string option
end = struct
  type t = (string, string) Hashtbl.t

  let create () = Hashtbl.create 16
  let add t name source = Hashtbl.replace t name source
  let find t name = Hashtbl.find_opt t name
end

let wrap_input ~name binds =
  let span = match binds with
    | [] -> None
    | b :: _ -> S.Node.span b
  in
  let node x = S.Node.make ?span x in
  let name_node = node name in
  let struct_expr = node (S.EStruct binds) in
  let bval = node (S.BVal (name_node, struct_expr)) in
  let var_expr = node (S.EVar name_node) in
  let bincl = node (S.BIncl (S.Public, var_expr)) in
  [ bval; bincl ]
;;

module ETvar = Util.Existential (F.TVar)

(* Strip the EExists layers introduced by packing module existentials,
   cloning each tvar into [check_env] and substituting in the body. *)
let unwrap_exists check_env aks packed_t =
  let rec loop env aks t =
    match aks with
    | [] -> env, t
    | ETvar.Ex a :: rest ->
      (match t with
       | F.Type.TExists (a', s) ->
         (match F.Kind.hequal (F.TVar.kind a) (F.TVar.kind a') with
          | Some Equal ->
            let cloned, env = F.Typecheck.Env.add_typ a env in
            let s = F.Type.Subst.subst_tvar a' cloned s in
            loop env rest s
          | None ->
            Format.kasprintf failwith "session: kind mismatch in unwrap_exists")
       | _ ->
         Format.kasprintf failwith
           "session: expected TExists at level %d in unwrap_exists, got %a"
           (List.length aks) F.Type.pp t)
  in
  loop check_env aks packed_t
;;

let rec unwrap_packs n v =
  if n = 0
  then v
  else (
    match v with
    | F.Value.VPack inner -> unwrap_packs (n - 1) inner
    | _ -> failwith "session: expected VPack in unwrap_packs")
;;

type fomega_state =
  { elab_env : Elaborate.Env.t
  ; check_env : F.Typecheck.Env.t
  ; eval_env : F.Eval.Env.t
  }

type typed_state = { eval_env : Eval.Env.t }

type mode_state =
  | MTyped of typed_state
  | MFOmega of fomega_state

type t =
  { sources : Sources.t
  ; mutable tc_env : Typecheck.Env.t
  ; mutable mode : mode_state
  ; mutable counter : int
  }

let init ~fomega () =
  let sources = Sources.create () in
  let mode =
    if fomega
    then
      MFOmega
        { elab_env = Elaborate.Env.empty
        ; check_env = F.Typecheck.Env.empty
        ; eval_env = F.Eval.Env.init (Eval.Extern.Compat.rossberg Eval.Extern.rossberg)
        }
    else MTyped { eval_env = Eval.Env.init Eval.Extern.rossberg }
  in
  { sources; tc_env = Typecheck.Env.empty; mode; counter = 0 }
;;

let read t name =
  match Sources.find t.sources name with
  | Some _ as some -> some
  | None -> Util.Diagnostic.read name
;;

let cache_source t ~filename ~source = Sources.add t.sources filename source
let next_id t = t.counter + 1
let next_filename t = Printf.sprintf "<repl-%d>" (next_id t)
let next_module_name t = Printf.sprintf "repl_input_%d" (next_id t)

(* For the typed-tree mode, just process each typed bind individually
   through Eval.Eval.bind — the typed-tree evaluator is naturally incremental. *)
let step_typed (state : typed_state) (typed_binds : T.Expr.bind list) =
  let eval_env = List.fold_left Eval.Eval.bind state.eval_env typed_binds in
  { eval_env }
;;

(* For the F-omega mode, we elaborate the step's binds as a single [EStruct]
   against an elab_env that has the step's module tvar pre-installed, evaluate
   the resulting packed F-omega expression once, then strip the existential
   layers it introduces and extend the check_env / eval_env with the values
   so that future steps can see them. *)
let step_fomega
      (state : fomega_state)
      (a : T.TVar.t)
      (typed_binds : T.Expr.bind list)
      (ts : (T.Var.t * T.Type.t) list)
  =
  (* Process the step as a single EStruct, just like Typecheck.Check.file does
     after wrapping. We pre-add the step's module tvar to elab_env so that
     paths the typechecker generated for this step can be resolved. *)
  let elab_env_with_a, _ = Elaborate.Env.add_tvar a state.elab_env in
  let elab_env_step = Elaborate.Env.enter_mod a elab_env_with_a in
  let typed_expr = T.Expr.EStruct (typed_binds, ts) in
  let aks, e_fomega = Elaborate.Elab.expr elab_env_step typed_expr in
  let packed_t = F.Typecheck.check state.check_env e_fomega in
  let check_env, inner_t = unwrap_exists state.check_env aks packed_t in
  let packed_v = F.Eval.eval state.eval_env e_fomega in
  let inner_v = unwrap_packs (List.length aks) packed_v in
  let inner_fields =
    match inner_t with
    | F.Type.TRecord fs -> fs
    | _ -> failwith "session: expected record type from module"
  in
  let inner_vals =
    match inner_v with
    | F.Value.VRecord vs -> vs
    | _ -> failwith "session: expected record value from module"
  in
  (* For each public field, allocate a fresh fomega var, bind it in
     elab_env (for future surface lookups), and bind its type/value in the
     fomega envs (so future inferences and evals find them). *)
  let elab_env, check_env, eval_env =
    List.fold_left
      (fun (elab_env, check_env, eval_env) (x, _) ->
         let name = T.Var.name x in
         let elab_env, fv = Elaborate.Env.add_var x elab_env in
         let t = List.assoc name inner_fields in
         let v = List.assoc name inner_vals in
         let check_env = F.Typecheck.Env.add_var fv t check_env in
         let eval_env = F.Eval.Env.add_var fv v eval_env in
         elab_env, check_env, eval_env)
      (elab_env_with_a, check_env, state.eval_env)
      ts
  in
  { elab_env; check_env; eval_env }
;;

let step t ~source parsed_binds =
  let filename = next_filename t in
  let name = next_module_name t in
  Sources.add t.sources filename source;
  let wrapped = wrap_input ~name parsed_binds in
  let a, set_kind = T.TVar.defer () in
  let tc_env_step = Typecheck.Env.enter_mod a t.tc_env in
  let tc_env_step, typed_pairs =
    List.fold_left_map Typecheck.Check.bind tc_env_step wrapped
  in
  let typed_binds = List.map (fun (_, _, _, b) -> b) typed_pairs in
  let all_kinds = List.concat_map (fun (ks, _, _, _) -> ks) typed_pairs in
  let all_ts =
    List.concat_map (fun (_, _, ts, _) -> ts) typed_pairs |> T.Var.normalize
  in
  set_kind (Option.value (T.Kind.opt_record all_kinds) ~default:T.Kind.empty);
  let mode =
    match t.mode with
    | MTyped state -> MTyped (step_typed state typed_binds)
    | MFOmega state -> MFOmega (step_fomega state a typed_binds all_ts)
  in
  t.tc_env <- tc_env_step;
  t.mode <- mode;
  t.counter <- t.counter + 1
;;
