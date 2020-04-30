module FLispy.ParseExtension

let gensym =
    let prefix = sprintf "x@%d"
    let mutable n = -1
    fun () ->
        n <- n + 1
        prefix n

let private elementaryOperations =
    let ops = [
        "=", ["*dummy-type*"; "*dummy-type*"; "Bool"]
        "distinct", ["*dummy-type*"; "*dummy-type*"; "Bool"]
        ">", ["Int"; "Int"; "Bool"]
        "<", ["Int"; "Int"; "Bool"]
        "<=", ["Int"; "Int"; "Bool"]
        ">=", ["Int"; "Int"; "Bool"]
        "+", ["Int"; "Int"; "Int"]
        "-", ["Int"; "Int"; "Int"]
        "*", ["Int"; "Int"; "Int"]
        "mod", ["Int"; "Int"; "Int"]
        "div", ["Int"; "Int"; "Int"]
        "=>", ["Bool"; "Bool"; "Bool"]
    ]
    let ops = List.map (fun ((op, _) as os) -> op, ElementaryOperation(os)) ops
    Map.ofList ops
let private hence = let f = Map.find "=>" elementaryOperations in fun t1 t2 -> Apply(f, [t1; t2])
let private equal = let f = Map.find "=" elementaryOperations in fun t1 t2 -> Apply(f, [t1; t2])

module private Operation =
    let argumentTypes = function
        | ElementaryOperation(_, _::s)
        | UserDefinedOperation(_, _::s) -> s
        | _ -> __unreachable__()

    let private returnTypeOfSignature = List.head
    let returnType = function
        | ElementaryOperation(_, s)
        | UserDefinedOperation(_, s) -> returnTypeOfSignature s
    
    let makeOperationSortsFromTypes sorts retSort = retSort :: sorts
    let makeOperationSortsFromVars vars retSort = makeOperationSortsFromTypes (List.map snd vars) retSort
    let makeUserOperationFromVars name vars retSort = UserDefinedOperation(name, makeOperationSortsFromVars vars retSort)
    let makeUserOperationFromSorts name artSorts retSort = UserDefinedOperation(name, makeOperationSortsFromTypes artSorts retSort)
    let makeElementaryOperationFromVars name vars retSort = ElementaryOperation(name, makeOperationSortsFromVars vars retSort)
    let makeElementaryOperationFromSorts name artSorts retSort = ElementaryOperation(name, makeOperationSortsFromTypes artSorts retSort)

    let generateReturnArgument sign =
        let retType = returnTypeOfSignature sign
        let retArg = gensym (), retType
        let retVar = Ident retArg
        retArg, retVar

let rec typeOf = function
    | Constant(Number _) -> "Int"
    | Forall _
    | Exists _
    | And _
    | Or _
    | Not _
    | Constant(Bool _) -> "Bool"
    | Ident(_, t) -> t
    | Apply(op, _) -> Operation.returnType op
    | Match(_, ((_, t)::_))
    | Ite(_, t, _)
    | Let(_, t) -> typeOf t
    | Match(_, []) -> __unreachable__()

let private to_sorted_vars = List.map (function PList [PSymbol v; PSymbol s] -> v, s | _ -> __unreachable__())
let private to_var_binding = List.map (function PList [PSymbol v; t] -> v, t | _ -> __unreachable__())
let private extend_env env vars = List.fold (fun typer (v, s) -> Map.add v s typer) env vars
let private create_env = extend_env Map.empty
let private tryTypeCheck f typer = Option.map Operation.returnType (Map.tryFind f typer)
let private getOperation f typer =
    match Map.tryFind f typer with
    | Some r -> r
    | _ -> failwithf "Unknown type: %s" f
let private typeGet x (typer, env) =
    match Map.tryFind x env with
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
            (v, e), Map.add v (typeOf e) env
        let bindings = to_var_binding bindings
        let bindings, env = List.mapFold handle_binding env bindings
        let body = toExpr (typer, env) body
        Let(bindings, body)
    | PList [PSymbol "forall"; PList vars; body] ->
        let vars = to_sorted_vars vars
        let env = extend_env env vars
        Forall(vars, toExpr (typer, env) body)
    | PList [PSymbol "exists"; PList vars; body] ->
        let vars = to_sorted_vars vars
        let env = extend_env env vars
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
                let id = Ident(v, typ)
                match tryTypeCheck v typer with
                | Some _ -> id, env
                | None -> id, Map.add v typ env
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
    let toComm typer e =
        let define_fun name vars sort body constr =
            let vars = to_sorted_vars vars
            let typer = Map.add name (Operation.makeUserOperationFromVars name vars sort) typer
            let env = create_env vars
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
                let fs = List.map2 (fun body (name, vars, sort) -> name, vars, sort, toExpr (typer, create_env vars) body) bodies signs
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
                Assert(toExpr (typer, Map.empty) expr), typer
            | PList [PSymbol "declare-sort"; PSymbol sort; PNumber 0] -> DeclareSort(sort), typer
            | PList [PSymbol "declare-const"; PSymbol name; PSymbol sort] ->
                DeclareConst(name, sort), Map.add name (Operation.makeUserOperationFromSorts name [] sort) typer
            | PList [PSymbol "declare-fun"; PSymbol name; PList argTypes; PSymbol sort] ->
                let argTypes = argTypes |> List.map (function PSymbol t -> t | _ -> __unreachable__())
                DeclareFun(name, argTypes, sort), Map.add name (Operation.makeUserOperationFromSorts name argTypes sort) typer
            | e -> failwithf "%O" e
        command_mapper typer comm, typer
    let comms, _ = List.mapFold toComm elementaryOperations exprs
    comms

let mapThird f = List.map (fun (v, a, r) -> v, a, f r)

let rec private expr_to_clauses typer env = function
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
    | Apply(op, args) ->
        let args = product typer env args
        let fallback_apply (v, a, rs) = v, a, Apply(op, rs)
        let app =
            match op with
            | ElementaryOperation _ -> fallback_apply
            | UserDefinedOperation(_, sign) ->
                let retArg, retVar = Operation.generateReturnArgument sign
                fun (vars, assumptions, args) ->
                let expr = Apply(op, retVar::args)
                (retArg::vars), (expr::assumptions), retVar
        List.map app args
    | Constant _
    | Ident _ as e -> [[], [], e]
    | Match(t, cases) ->
        let rec get_free_vars = function
            | Apply(_, ts) -> List.collect get_free_vars ts
            | Ident(name, _) when Map.containsKey name typer -> []
            | Ident(v, t) -> [v, t]
            | _ -> __unreachable__()
        let handle_case (pattern, body) =
            let pat_match = equal t pattern
            let vars = get_free_vars pattern
            let env = extend_env env vars
            expr_to_clauses typer env body
            |> List.map (fun (vars', assumptions, body) -> vars @ vars', pat_match::assumptions, body)
        List.collect handle_case cases
    | Let(bindings, body) ->
        let rec handle_bindings env = function
            | [] -> expr_to_clauses typer env body
            | (var, body)::bindings ->
                let typ = typeOf body
                let id = var, typ
                let varTerm = Ident id
                let body_clauses = expr_to_clauses typer env body
                let rest = handle_bindings (Map.add var typ env) bindings
                collector {
                    let! vb, ab, rb = body_clauses
                    let! vr, ar, rr = rest
                    return id :: vb @ vr, (equal varTerm rb) :: ab @ ar, rr
                }
        handle_bindings env bindings
    | Not e -> mapInside typer env e Not
    | Or cases -> product typer env cases |> mapThird Or
    | And exprs -> product typer env exprs |> mapThird And
    | Forall(vars, e) -> mapInside typer env e (fun e -> Forall(vars, e))
    | Exists(vars, e) -> mapInside typer env e (fun e -> Exists(vars, e))
and product typer env args =
    let combine2 arg st =
        let arg = expr_to_clauses typer env arg
        collector {
            let! v, a, r = st
            let! v', a', r' = arg
            return v' @ v, a' @ a, r' :: r
        }
    List.foldBack combine2 args [[], [], []]
and mapInside typer env e constructor = expr_to_clauses typer env e |> mapThird constructor

let definition_to_clauses typer (name, vars, sort, body) =
    let sign = Operation.makeOperationSortsFromVars vars sort
    let retArg, retVar = Operation.generateReturnArgument sign
    let vars = retArg :: vars
    let env = create_env vars
    let app = Apply(getOperation name typer, List.map Ident vars)
    let handle_clause (clvars, assumptions, retExpr) =
        let body = equal retVar retExpr :: assumptions
        Assert(Forall(vars @ clvars, hence (And body) app))
    let bodies =
        expr_to_clauses typer env body
        |> List.map handle_clause
    DeclareFun(name, sign, "Bool")::bodies

let comm_to_clauses typer = function
    | CheckSat
    | DeclareSort _
    | DeclareConst _
    | DeclareFun _
    | DeclareDatatypes _
    | DeclareDatatype _ as c -> [[c]]
    | DefineFun df
    | DefineFunRec df -> definition_to_clauses typer df |> List.map List.singleton
    | DefineFunsRec dfs -> List.collect (definition_to_clauses typer) dfs |> List.map List.singleton
    | Assert query ->
        expr_to_clauses typer Map.empty query
        |> List.map (fun (vars, assumptions, body) -> Assert(Forall(vars, hence (And assumptions) body)))
        |> List.singleton
    | c -> failwithf "Can't obtain clauses from: %O" c

let exprsToSetOfCHCSystems = parseToTerms comm_to_clauses >> List.concat >> List.product

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

let to_cvc4 exprs =
    let setOfCHCSystems = exprsToSetOfCHCSystems exprs
    let set_logic_all = SetLogic "ALL"
    setOfCHCSystems |> List.map (fun chcSystem -> set_logic_all :: List.collect to_sorts chcSystem)
