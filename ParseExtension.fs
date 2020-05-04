module FLispy.ParseExtension
open FLispy.Operations
open FLispy.PropagateNot

module IntToNat =
    let private nat_sort = gensymp "Nat"
    let private Z_constr = gensymp "Z"
    let private S_constr = gensymp "S"
    let private unS_constr = gensymp "unS"
    let private S_op = Operation.makeElementaryOperationFromSorts S_constr [nat_sort] nat_sort
    let private Z = Ident(Z_constr, nat_sort)
    let private S t = Apply(S_op, [t])
    let sort s = if s = "Int" then nat_sort else s
    let sort_list = List.map sort
    let sorted_var (v, t) = v, sort t
    let sorted_var_list = List.map sorted_var
    let constructor (c, ts) = c, sorted_var_list ts
    let constructor_list = List.map constructor
    let definition (name, args, ret, body) = name, sorted_var_list args, sort ret, body

    let rec int_to_nat n = if n <= 0 then Z else S (int_to_nat (n - 1))

    module private V =
        let x = gensymp "x"
        let y = gensymp "y"
        let r = gensymp "r"
        let z = gensymp "z"
        let xvar = (x, nat_sort)
        let yvar = (y, nat_sort)
        let rvar = (r, nat_sort)
        let zvar = (z, nat_sort)
        let xid = Ident xvar
        let yid = Ident yvar
        let rid = Ident rvar
        let zid = Ident zvar

    let private nat_datatype = DeclareDatatype(nat_sort, [Z_constr, []; S_constr, [unS_constr, nat_sort]])
    let private add_name = gensymp "add"
    let private add_sorts = Operation.makeOperationSortsFromTypes [nat_sort; nat_sort] nat_sort
    let private add_op = ElementaryOperation(add_name, Operation.makeOperationSortsFromTypes add_sorts "Bool")
    let private add_app x y r = Operation.makeApp add_op [x; y] r
    let private add_decl =
        [
            DeclareFun(add_name, add_sorts, "Bool")
            Assert(Forall([V.yvar], hence [] (add_app Z V.yid V.yid)))
            Assert(Forall([V.xvar; V.yvar; V.rvar], hence [add_app V.xid V.yid V.rid] (add_app (S V.xid) V.yid (S V.rid))))
        ]
    let private minus_name = gensymp "minus"
    let private minus_sorts = add_sorts
    let private minus_op = ElementaryOperation(minus_name, Operation.makeOperationSortsFromTypes minus_sorts "Bool")
    let private minus_app x y r = Operation.makeApp minus_op [x; y] r
    let private minus_decl =
        [
            DeclareFun(minus_name, minus_sorts, "Bool")
            Assert(Forall([V.yvar], hence [] (minus_app Z V.yid Z)))
            Assert(Forall([V.xvar; V.yvar; V.rvar], hence [minus_app V.xid V.yid V.rid] (minus_app (S V.xid) V.yid (S V.rid))))
        ]
    let private le_name = gensymp "le"
    let private le_sorts = [nat_sort; nat_sort]
    let private le_op = ElementaryOperation(le_name, Operation.makeOperationSortsFromTypes le_sorts "Bool")
    let private le_app x y = Apply(le_op, [x; y])
    let private le_decl =
        [
            DeclareFun(le_name, le_sorts, "Bool")
            Assert(Forall([V.yvar], hence [] (le_app Z V.yid)))
            Assert(Forall([V.xvar; V.yvar], hence [le_app V.xid V.yid] (le_app (S V.xid) (S V.yid))))
        ]
    let private ge_name = gensymp "ge"
    let private ge_sorts = [nat_sort; nat_sort]
    let private ge_op = ElementaryOperation(ge_name, Operation.makeOperationSortsFromTypes ge_sorts "Bool")
    let private ge_app x y = Apply(ge_op, [x; y])
    let private ge_decl =
        [
            DeclareFun(ge_name, ge_sorts, "Bool")
            Assert(Forall([V.yvar], hence [] (ge_app V.yid Z)))
            Assert(Forall([V.xvar; V.yvar], hence [ge_app V.xid V.yid] (ge_app (S V.xid) (S V.yid))))
        ]
    let private lt_name = gensymp "lt"
    let private lt_sorts = [nat_sort; nat_sort]
    let private lt_op = ElementaryOperation(lt_name, Operation.makeOperationSortsFromTypes lt_sorts "Bool")
    let private lt_app x y = Apply(lt_op, [x; y])
    let private lt_decl =
        [
            DeclareFun(lt_name, lt_sorts, "Bool")
            Assert(Forall([V.yvar], hence [] (lt_app Z (S V.yid))))
            Assert(Forall([V.xvar; V.yvar], hence [lt_app V.xid V.yid] (lt_app (S V.xid) (S V.yid))))
        ]
    let private gt_name = gensymp "gt"
    let private gt_sorts = [nat_sort; nat_sort]
    let private gt_op = ElementaryOperation(gt_name, Operation.makeOperationSortsFromTypes gt_sorts "Bool")
    let private gt_app x y = Apply(gt_op, [x; y])
    let private gt_decl =
        [
            DeclareFun(gt_name, gt_sorts, "Bool")
            Assert(Forall([V.yvar], hence [] (gt_app (S V.yid) Z)))
            Assert(Forall([V.xvar; V.yvar], hence [gt_app V.xid V.yid] (gt_app (S V.xid) (S V.yid))))
        ]
    let private mult_name = gensymp "mult"
    let private mult_sorts = Operation.makeOperationSortsFromTypes [nat_sort; nat_sort] nat_sort
    let private mult_op = ElementaryOperation(mult_name, Operation.makeOperationSortsFromTypes mult_sorts "Bool")
    let private mult_app x y r = Operation.makeApp mult_op [x; y] r
    let private mult_decl =
        [
            DeclareFun(mult_name, mult_sorts, "Bool")
            Assert(Forall([V.yvar], hence [] (mult_app Z V.yid Z)))
            Assert(Forall([V.xvar; V.yvar; V.rvar; V.zvar], hence [mult_app V.xid V.yid V.rid; add_app V.rid V.yid V.zid] (mult_app (S V.xid) V.yid V.zid)))
        ]
    let private div_name = gensymp "div"
    let private div_sorts = Operation.makeOperationSortsFromTypes [nat_sort; nat_sort] nat_sort
    let private div_op = ElementaryOperation(div_name, Operation.makeOperationSortsFromTypes div_sorts "Bool")
    let private div_app x y r = Operation.makeApp div_op [x; y] r
    let private div_decl =
        [
            DeclareFun(div_name, div_sorts, "Bool")
            Assert(Forall([V.xvar; V.yvar], hence [lt_app V.xid V.yid] (div_app V.xid V.yid Z)))
            Assert(Forall([V.xvar; V.yvar; V.rvar; V.zvar], hence [ge_app V.xid V.yid; minus_app V.xid V.yid V.zid; div_app V.zid V.yid V.rid] (div_app V.xid V.yid (S V.rid))))
        ]
    let private mod_name = gensymp "mod"
    let private mod_sorts = Operation.makeOperationSortsFromTypes [nat_sort; nat_sort] nat_sort
    let private mod_op = ElementaryOperation(mod_name, Operation.makeOperationSortsFromTypes mod_sorts "Bool")
    let private mod_app x y r = Operation.makeApp mod_op [x; y] r
    let private mod_decl =
        [
            DeclareFun(mod_name, mod_sorts, "Bool")
            Assert(Forall([V.xvar; V.yvar], hence [lt_app V.xid V.yid] (mod_app V.xid V.yid V.xid)))
            Assert(Forall([V.xvar; V.yvar; V.rvar; V.zvar], hence [ge_app V.xid V.yid; minus_app V.xid V.yid V.zid; mod_app V.zid V.yid V.rid] (mod_app V.xid V.yid V.rid)))
        ]

    let substitutions = Map.ofList [
        "+", (add_op, true)
        "-", (minus_op, true)
        "*", (mult_op, true)
        "div", (div_op, true)
        "mod", (mod_op, true)
        "<=", (le_op, false)
        ">=", (ge_op, false)
        "<", (gt_op, false)
        ">", (lt_op, false)
    ]
    let declarations = nat_datatype :: add_decl @ minus_decl @ le_decl @ ge_decl @ lt_decl @ gt_decl @ mult_decl @ div_decl @ mod_decl

let private to_sorted_vars = List.map (function PList [PSymbol v; PSymbol s] -> v, s | _ -> __unreachable__())
let private to_var_binding = List.map (function PList [PSymbol v; t] -> v, t | _ -> __unreachable__())

module VarEnv =
    type sorted_var = string * sort
    type env = Map<string, sort> * Map<string, string>

    let empty : env = Map.empty, Map.empty

    let get (env_sorts, env_vars) ((var, sort) as vs) : sorted_var =
        match Map.tryFind var env_sorts with
        | Some sort' when sort = sort' -> vs
        | Some sort' -> failwithf "Environment has sort %O of %O (%O)" sort' var sort
        | None ->
            match Map.tryFind var env_vars with
            | Some var' ->
                match Map.tryFind var' env_sorts with
                | Some sort' when sort = sort' -> var', sort
                | Some sort' -> failwithf "Environment has alias %O with sort %O for %O (%O)" var' sort' var sort
                | None -> failwithf "Environment has no sort for alias %O of %O (%O)" var' var sort
            | None -> failwithf "Environment has neither sort neither alias for %O (%O)" var sort

    let extendOne (env_sorts, env_vars) ((var : string), sort) : sorted_var * env=
        let var', env_vars =
            if var.StartsWith("_") then
                let var' = gensym ()
                let env_vars = Map.add var var' env_vars
                var', env_vars
            elif Map.containsKey var env_sorts then
                let var' = gensymp var
                let env_vars = Map.add var var' env_vars
                var', env_vars
            else var, env_vars
        let env_sorts = Map.add var' sort env_sorts
        (var', sort), (env_sorts, env_vars)

    let extend env vars = List.mapFold extendOne env vars
    let create vars : env = vars |> extend empty |> snd

    let typeCheck (env_sorts, env_vars) x =
        match Map.tryFind x env_sorts with
        | Some _ as t -> t
        | None ->
            match Map.tryFind x env_vars with
            | Some y -> Map.tryFind y env_sorts
            | None -> None

let private tryTypeCheck f typer = Option.map Operation.returnType (Map.tryFind f typer)
let private getOperation f typer =
    match Map.tryFind f typer with
    | Some r -> r
    | _ -> failwithf "Unknown type: %s" f
let private typeGet x (typer, env) =
    match VarEnv.typeCheck env x with
    | Some t -> t
    | None ->
        match tryTypeCheck x typer with
        | Some t -> t
        | None -> failwithf "Unknown type: %s" x

let rec private toExpr ((typer, env) as te) = function
    | PNumber n -> Constant (Number n)
    | PSymbol "true" -> Constant (Bool true)
    | PSymbol "false" -> Constant (Bool false)
    | PList [] -> __unreachable__()
    | PList [PSymbol "let"; PList bindings; body] ->
        let handle_binding env (v, e) =
            let e = toExpr (typer, env) e
            let (v, _), env = VarEnv.extendOne env (v, typeOf e)
            (v, e), env
        let bindings = to_var_binding bindings
        let bindings, env = List.mapFold handle_binding env bindings
        let body = toExpr (typer, env) body
        Let(bindings, body)
    | PList [PSymbol "forall"; PList vars; body] ->
        let vars = to_sorted_vars vars
        let vars, env = VarEnv.extend env vars
        Forall(vars, toExpr (typer, env) body)
    | PList [PSymbol "exists"; PList vars; body] ->
        let vars = to_sorted_vars vars
        let vars, env = VarEnv.extend env vars
        Exists(vars, toExpr (typer, env) body)
    | PList (op::args) ->
        let args = List.map (toExpr te) args
        match op, args with
        | PSymbol "ite", [i; t; e] -> Ite(i, t, e)
        | PSymbol "and", _ -> And args
        | PSymbol "or", _ -> Or args
        | PSymbol "not", [arg] -> Not arg
        | PSymbol f, args ->
            let op = getOperation f typer
            Apply(op, args)
        | e -> failwithf "%O" e
    | PSymbol x -> Ident(x, typeGet x te)
    | PMatch(t, cases) ->
        let t = toExpr te t
        let typ = typeOf t
        let extendEnvironment env = function
            | PSymbol v, typ ->
                let vt = (v, typ)
                match tryTypeCheck v typer with
                | Some _ -> Ident vt, env
                | None ->
                    let vt, env = VarEnv.extendOne env vt
                    Ident vt, env
            | _ -> __unreachable__()
        let handle_case (pat, body) =
            match pat with
            | PList (PSymbol constr::cargs) ->
                let op = getOperation constr typer
                let cargs, env = List.mapFold extendEnvironment env (List.zip cargs (Operation.argumentTypes op))
                Apply(op, cargs), toExpr (typer, env) body
            | _ ->
                let v, env = extendEnvironment env (pat, typ)
                v, toExpr (typer, env) body
        let cases = List.map handle_case cases
        Match(t, cases)

let parseToTerms command_mapper exprs =
    let toComm (typer, diseqs) e =
        let define_fun name vars sort body constr =
            let vars = to_sorted_vars vars
            let typer = Map.add name (Operation.makeUserOperationFromVars name vars sort) typer
            let env = VarEnv.create vars
            let body = toExpr (typer, env) body
            constr(name, vars, sort, body), typer
        let parse_constructors typer adtname constrs =
            let handle_constr typer = function
                | PList (PSymbol fname::vars) ->
                    let vars = to_sorted_vars vars
                    let typer = List.fold (fun typer (pr, s) -> Map.add pr (Operation.makeElementaryOperationFromSorts pr [adtname] s) typer) typer vars
                    let typer = Map.add fname (Operation.makeElementaryOperationFromVars fname vars adtname) typer
                    (fname, vars), typer
                | _ -> __unreachable__()
            List.mapFold handle_constr typer constrs
        let comm, typer =
            match e with
            | PList [PSymbol "define-fun"; PSymbol name; PList vars; PSymbol sort; body] ->
                define_fun name vars sort body DefineFun
            | PList [PSymbol "define-fun-rec"; PSymbol name; PList vars; PSymbol sort; body] ->
                define_fun name vars sort body DefineFunRec
            | PList [PSymbol "define-funs-rec"; PList signs; PList bodies] ->
                let signs = signs |> List.map (function PList [PSymbol name; PList vars; PSymbol sort] -> name, to_sorted_vars vars, sort | _ -> __unreachable__())
                let typer = List.fold (fun typer (name, vars, sort) -> Map.add name (Operation.makeUserOperationFromVars name vars sort) typer) typer signs
                let fs = List.map2 (fun body (name, vars, sort) -> name, vars, sort, toExpr (typer, VarEnv.create vars) body) bodies signs
                DefineFunsRec fs, typer
            | PList [PSymbol "declare-datatype"; PSymbol adtname; PList constrs] ->
                let constrs, typer = parse_constructors typer adtname constrs
                DeclareDatatype(adtname, constrs), typer
            | PList [PSymbol "declare-datatypes"; PList signs; PList constr_groups] ->
                let names = signs |> List.map (function PList [PSymbol name; PNumber 0] -> name | _ -> __unreachable__())
                let dfs, typer = List.mapFold (fun typer (name, PList constrs) -> parse_constructors typer name constrs) typer (List.zip names constr_groups)
                DeclareDatatypes (List.zip names dfs), typer
            | PList [PSymbol "check-sat"] -> CheckSat, typer
            | PList [PSymbol "assert"; expr] ->
                Assert(toExpr (typer, VarEnv.empty) expr), typer
            | PList [PSymbol "declare-sort"; PSymbol sort; PNumber 0] -> DeclareSort(sort), typer
            | PList [PSymbol "declare-const"; PSymbol name; PSymbol sort] ->
                DeclareConst(name, sort), Map.add name (Operation.makeUserOperationFromSorts name [] sort) typer
            | PList [PSymbol "declare-fun"; PSymbol name; PList argTypes; PSymbol sort] ->
                let argTypes = argTypes |> List.map (function PSymbol t -> t | _ -> __unreachable__())
                DeclareFun(name, argTypes, sort), Map.add name (Operation.makeUserOperationFromSorts name argTypes sort) typer
            | PList [PSymbol "set-logic"; PSymbol name] -> SetLogic(name), typer
            | e -> failwithf "%O" e
        let preamb, comm, diseqs = PropagateNot.propagateNot typer diseqs comm
        command_mapper typer comm @ List.map List.singleton preamb, (typer, diseqs)
    let comms, _ = List.mapFold toComm (elementaryOperations, Diseq.empty) exprs
    comms

let mapThird f = List.map (fun (v, a, r) -> v, a, f r)

let private apply_with_new_return_arg op sign =
    let retArg, retVar = Operation.generateReturnArgument (IntToNat.sort_list sign)
    fun (vars, assumptions, args) ->
    let expr = Operation.makeApp op args retVar
    (retArg::vars), (expr::assumptions), retVar

let private fallback_apply op (v, a, rs) = v, a, Apply(op, rs)

let private expr_to_clauses map_user_operation typer env command =
    let rec expr_to_clauses typer env = function
        | Ident(name, _) as e when Map.containsKey name typer ->
            match Map.find name typer with
            | UserDefinedOperation _ as op ->
                expr_to_clauses typer env (Apply(op, []))
            | ElementaryOperation _ -> [[], [], e]
        | Constant(Number n) -> [[], [], IntToNat.int_to_nat n]
        | Constant _ as e -> [[], [], e]
        | Ident(name, sort) -> [[], [], Ident <| VarEnv.get env (name, IntToNat.sort sort)]
        | Apply(op, args) ->
            let args = product typer env args
            let app =
                match op with
                | ElementaryOperation(name, sign) ->
                    match Map.tryFind name IntToNat.substitutions with
                    | Some(op, true) -> apply_with_new_return_arg op sign
                    | Some(op, false) -> fallback_apply op
                    | None -> fallback_apply op
                | UserDefinedOperation(_, sign) -> map_user_operation op sign
            List.map app args
        | Not e -> expr_to_clauses typer env e |> mapThird Not
        | Or cases -> product typer env cases |> mapThird Or
        | And exprs -> product typer env exprs |> mapThird And
        | Forall(vars, e) -> mapInsideQuantifier typer env vars e Forall
        | Exists(vars, e) -> mapInsideQuantifier typer env vars e Exists
        | Ite(i, t, e) ->
            let i = expr_to_clauses typer env i
            let t = expr_to_clauses typer env t
            let e = expr_to_clauses typer env e
            collector {
                let! ivars, iassumptions, iretExpr = i
                let! tvars, tassumptions, tretExpr = t
                let! evars, eassumptions, eretExpr = e
                return ivars @ tvars @ evars, iassumptions @ tassumptions @ eassumptions, Ite(iretExpr, tretExpr, eretExpr)
            }
        | Match(t, cases) ->
            let rec get_free_vars = function
                | Apply(_, ts) -> List.collect get_free_vars ts
                | Ident(name, _) when Map.containsKey name typer -> []
                | Ident(v, t) -> [v, t]
                | _ -> __unreachable__()
            let handle_case (pattern, body) =
                let vars = get_free_vars pattern
                let vars, env = VarEnv.extend env (IntToNat.sorted_var_list vars)
                expr_to_clauses typer env body
                |> List.map (fun (vars', assumptions, body) -> pattern, vars @ vars', assumptions, body)
            let t = expr_to_clauses typer env t
            let cases = List.collect handle_case cases
            collector {
                let! tvars, tassumptions, tretExpr = t
                let! pattern, brvars, brassumptions, brretExpr = cases
                let pat_match = equal tretExpr pattern
                return tvars @ brvars, pat_match :: tassumptions @ brassumptions, brretExpr
            }
        | Let(bindings, body) ->
            let rec handle_bindings env = function
                | [] -> expr_to_clauses typer env body
                | (var, body)::bindings ->
                    let typ = typeOf body
                    let body_clauses = expr_to_clauses typer env body
                    let id, env = VarEnv.extendOne env (IntToNat.sorted_var (var, typ))
                    let varTerm = Ident id
                    let rest = handle_bindings env bindings
                    collector {
                        let! vb, ab, rb = body_clauses
                        let! vr, ar, rr = rest
                        return id :: vb @ vr, (equal varTerm rb) :: ab @ ar, rr
                    }
            handle_bindings env bindings
    and product typer env args =
        let combine2 arg st =
            let arg = expr_to_clauses typer env arg
            collector {
                let! v, a, r = st
                let! v', a', r' = arg
                return v' @ v, a' @ a, r' :: r
            }
        List.foldBack combine2 args [[], [], []]
    and mapInsideQuantifier typer env vars e constructor =
        let vars, env = VarEnv.extend env (IntToNat.sorted_var_list vars)
        expr_to_clauses typer env e
        |> List.map (fun (vars', assumptions, result) -> [], [], constructor(vars, forall vars' (hence assumptions result)))
    expr_to_clauses typer env command

let private clauses_expr_to_clauses = expr_to_clauses (fun op _ -> fallback_apply op)
let private function_expr_to_clauses = expr_to_clauses apply_with_new_return_arg

let private relational_declaration name argSorts sort =
    DeclareFun(name, Operation.makeOperationSortsFromTypes argSorts sort, "Bool")

let private definition_to_clauses typer (name, vars, sort, body) =
    let sign = Operation.makeOperationSortsFromVars vars sort
    let retArg, retVar = Operation.generateReturnArgument sign
    let vars = retArg :: vars
    let env = VarEnv.create vars
    let app = Apply(getOperation name typer, List.map Ident vars)
    let handle_clause (clvars, assumptions, retExpr) =
        let body = equal retVar retExpr :: assumptions
        Assert(Forall(vars @ clvars, hence body app))
    let bodies =
        function_expr_to_clauses typer env body
        |> List.map handle_clause
    DeclareFun(name, sign, "Bool"), bodies

let private comm_to_clauses declaration expr_to_clauses typer = function
    | SetLogic _
    | CheckSat
    | DeclareSort _ as c -> [[c]]
    | DeclareDatatypes dfs ->
        let names, constrs = List.unzip dfs
        let constrs = constrs |> List.map IntToNat.constructor_list
        [[DeclareDatatypes(List.zip names constrs)]]
    | DeclareDatatype(name, cs) -> [[DeclareDatatype(name, IntToNat.constructor_list cs)]]
    | DeclareConst(name, sort) -> [[declaration (fun (n, _, s) -> DeclareConst(n, s)) name [] (IntToNat.sort sort)]]
    | DeclareFun(name, argSorts, sort) -> [[declaration DeclareFun name (IntToNat.sort_list argSorts) (IntToNat.sort sort)]]
    | DefineFun df
    | DefineFunRec df ->
        let df = IntToNat.definition df
        let dec, bodies = definition_to_clauses typer df
        dec :: bodies |> List.map List.singleton
    | DefineFunsRec dfs ->
        let decs, bodies = List.map (IntToNat.definition >> definition_to_clauses typer) dfs |> List.unzip
        decs @ List.concat bodies |> List.map List.singleton
    | Assert query ->
        expr_to_clauses typer VarEnv.empty query
        |> List.map (fun (vars, assumptions, body) -> Assert(forall vars <| hence assumptions body))
        |> List.singleton
    | c -> failwithf "Can't obtain clauses from: %O" c

let clauses_to_clauses = comm_to_clauses (fun constr name argSorts sort -> constr(name, argSorts, sort)) clauses_expr_to_clauses
let functions_to_clauses = comm_to_clauses (fun _ -> relational_declaration) function_expr_to_clauses

let exprsToSetOfCHCSystems to_clauses = parseToTerms to_clauses >> List.concat >> List.product >> List.map (List.append Diseq.preambula)

let private adt_df_to_sorted (typename, constructors) =
    let parse_constructor (name, args) = DeclareFun(name, List.map snd args, typename)
    let decsort = DeclareSort typename
    let decfuns = List.map parse_constructor constructors
    decsort, decfuns

let to_sorts = function
    | DeclareDatatypes dfs ->
        let dss, dfs = List.unzip <| List.map adt_df_to_sorted dfs
        dss @ List.concat dfs
    | DeclareDatatype(t, c) ->
        let decsort, decfuns = adt_df_to_sorted (t, c)
        decsort :: decfuns
    | e -> [e]

let to_cvc4 to_clauses exprs =
    let setOfCHCSystems = exprsToSetOfCHCSystems to_clauses exprs
    let set_logic_all = SetLogic "ALL"
    let get_info = GetInfo ":reason-unknown"
    setOfCHCSystems
    |> List.map (fun chcSystem -> List.collect to_sorts chcSystem @ [get_info])
    |> List.map (fun chcSystem -> chcSystem |> List.filter (function SetLogic _ -> false | _ -> true))
    |> List.map (fun chcSystem -> set_logic_all :: chcSystem)
