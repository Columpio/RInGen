module FLispy.ParseExtension
open FLispy
open FLispy.Operations
open FLispy.PropagateNot
open FLispy.ParseToTerms

let mapThird f = List.map (fun (v, a, r) -> v, a, f r)

let private apply_with_new_return_arg ts op sign =
    let retArg, retVar = Operation.generateReturnArgument (Typer.sort_list ts sign)
    fun (vars, assumptions, args) ->
    let expr = Operation.makeApp op args retVar
    (retArg::vars), (expr::assumptions), retVar

let private fallback_apply op (v, a, rs) = v, a, Apply(op, rs)

let rec private expr_to_clauses ((typer, _) as ts) env = function
    | Ident(name, _) as e when Map.containsKey name typer ->
        match Map.find name typer with
        | UserDefinedOperation _ as op ->
            expr_to_clauses ts env (Apply(op, []))
        | ElementaryOperation _ -> [[], [], e]
    | Constant(Number n) -> [[], [], IntToNat.int_to_nat n]
    | Constant _ as e -> [[], [], e]
    | Ident(name, sort) -> [[], [], Ident <| VarEnv.get env (name, Typer.sort ts sort)]
    | Apply(op, args) ->
        let args = product ts env args
        let app =
            match op with
            | ElementaryOperation(name, sign) ->
                match Map.tryFind name IntToNat.substitutions with
                | Some(op, true) -> apply_with_new_return_arg ts op sign
                | Some(op, false) -> fallback_apply op
                | None -> fallback_apply op
            | UserDefinedOperation(_, sign) -> apply_with_new_return_arg ts op sign
        List.map app args
    | Not e -> expr_to_clauses ts env e |> mapThird Not
    | Or cases -> product ts env cases |> mapThird Or
    | And exprs -> product ts env exprs |> mapThird And
    | Forall _
    | Exists _ -> __unreachable__()
//    | Forall(vars, e) -> mapInsideQuantifier typer env vars e Forall
//    | Exists(vars, e) -> mapInsideQuantifier typer env vars e Exists
    | Hence(cond, body) ->
        let cond = expr_to_clauses ts env cond
        let body = expr_to_clauses ts env body
        collector {
            let! cvars, cassumptions, cretExpr = cond
            let! bvars, bassumptions, bretExpr = body
            return cvars @ bvars, cretExpr :: cassumptions @ bassumptions, bretExpr
        }
    | Ite(i, t, e) ->
        let i = expr_to_clauses ts env i
        let t = expr_to_clauses ts env t
        let e = expr_to_clauses ts env e
        collector {
            let! ivars, iassumptions, iretExpr = i
            let! tvars, tassumptions, tretExpr = t
            let! evars, eassumptions, eretExpr = e
            return ivars @ tvars @ evars, iassumptions @ tassumptions @ eassumptions, Ite(iretExpr, tretExpr, eretExpr)
        }
    | Match(t, cases) ->
        let handle_case (pattern, body) =
            let vars = MatchExtensions.getFreeVarsFromPattern typer pattern
            let vars, env = VarEnv.extend env (Typer.sorted_var_list ts vars)
            let pattern = VarEnv.renameVars ts env pattern
            expr_to_clauses ts env body
            |> List.map (fun (vars', assumptions, body) -> pattern, vars @ vars', assumptions, body)
        let t = expr_to_clauses ts env t
        let cases = List.collect handle_case cases
        collector {
            let! tvars, tassumptions, tretExpr = t
            let! pattern, brvars, brassumptions, brretExpr = cases
            let pat_match = equal tretExpr pattern
            return tvars @ brvars, pat_match :: tassumptions @ brassumptions, brretExpr
        }
    | Let(bindings, body) ->
        let rec handle_bindings env = function
            | [] -> expr_to_clauses ts env body
            | (var, body)::bindings ->
                let typ = Typer.typeOf body
                let body_clauses = expr_to_clauses ts env body
                let id, env = VarEnv.extendOne env (Typer.sorted_var ts (var, typ))
                let varTerm = Ident id
                let rest = handle_bindings env bindings
                collector {
                    let! vb, ab, rb = body_clauses
                    let! vr, ar, rr = rest
                    return id :: vb @ vr, (equal varTerm rb) :: ab @ ar, rr
                }
        handle_bindings env bindings
and private product ts env args =
    let combine2 arg st =
        let arg = expr_to_clauses ts env arg
        collector {
            let! v, a, r = st
            let! v', a', r' = arg
            return v' @ v, a' @ a, r' :: r
        }
    List.foldBack combine2 args [[], [], []]
and private mapInsideQuantifier ts env vars e constructor =
    let vars, env = VarEnv.extend env (Typer.sorted_var_list ts vars)
    expr_to_clauses ts env e
    |> List.map (fun (vars', assumptions, result) -> [], [], constructor(vars, forall vars' (henceOrNot assumptions result)))
//expr_to_clauses typer env command

//let private clauses_expr_to_clauses = expr_to_clauses (fun op _ -> fallback_apply op)
//let private function_expr_to_clauses = expr_to_clauses apply_with_new_return_arg

let private relational_declaration name argSorts sort =
    DeclareFun(name, Operation.makeOperationSortsFromTypes argSorts sort, "Bool")

let private definition_to_clauses ts (name, vars, sort, body) =
    let sign = Operation.makeOperationSortsFromVars vars sort
    let retArg, retVar = Operation.generateReturnArgument sign
    let vars = retArg :: vars
    let vars = Typer.sorted_var_list ts vars
    let env = VarEnv.create vars
    let app = Apply(Typer.getOperation name ts, List.map Ident vars)
    let handle_clause (clvars, assumptions, retExpr) =
        let body = equal retVar retExpr :: assumptions
        Assert(Forall(vars @ clvars, hence body app))
    let bodies =
        expr_to_clauses ts env body
        |> List.map handle_clause
    DeclareFun(name, sign, "Bool"), bodies

let private niceAssertion e =
    match e with
    | Not(Forall _ as e) -> e
    | Forall _ as e -> e
    | Hence(Ident _, Constant(Bool false)) -> e
    | Apply _ -> e
    | _ -> failwithf "bad assertion: %O" e

let private collectAsserts cs =
    let rec iter cms asserts = function
        | [] ->
            let asserts = List.map niceAssertion asserts
            List.rev cms, List.rev asserts
        | CheckSat::cs -> iter cms asserts cs
        | Assert e::cs -> iter cms (e::asserts) cs
        | c::cs -> iter (c::cms) asserts cs
    iter [] [] cs

let private functionToClauses ts = function
    | GetInfo _
    | SetLogic _
    | CheckSat as c -> [[c]]
    | DeclareSort _ -> [] // substituted by Nats
    | DeclareDatatypes dfs ->
        let names, constrs = List.unzip dfs
        let constrs = constrs |> List.map (Typer.constructor_list ts)
        [[DeclareDatatypes(List.zip names constrs)]]
    | DeclareDatatype(name, cs) -> [[DeclareDatatype(name, Typer.constructor_list ts cs)]]
    | DeclareConst(name, sort) -> [[DeclareConst(name, Typer.sort ts sort)]]
    | DeclareFun _ -> __unreachable__() // Actually it allows high-order behavior
    | DefineFun df
    | DefineFunRec df ->
        let df = Typer.definition ts df
        let dec, bodies = definition_to_clauses ts df
        dec :: bodies |> List.map List.singleton
    | DefineFunsRec dfs ->
        let decs, bodies = List.map (Typer.definition ts >> definition_to_clauses ts) dfs |> List.unzip
        decs @ List.concat bodies |> List.map List.singleton
    | Assert query ->
        let Qs, env, query = TakeOutQuantifiers.takeOutQuantifiers ts query
        expr_to_clauses ts env query
        |> List.map (fun (vars, assumptions, body) -> Assert(hence (Not body :: assumptions) falsee |> forall vars |> Qs))
        |> List.singleton
    | c -> failwithf "Can't obtain clauses from: %O" c

let private functionCommandsToClausesSets cs = Typer.typerMap functionToClauses cs |> List.concat |> List.product

let private preambulize cs =
    Diseq.preambula @ cs

let functionsToClauses functionsToClauses ps =
    let cs = ps |> parseToTerms //|> unfoldDeclarations
    let cs', asserts = collectAsserts cs
    let cs'' = cs' @ List.map Assert asserts // [Assert (And asserts)]
    let css = if functionsToClauses then functionCommandsToClausesSets cs'' else [cs'']
    let css' = List.map (fun cs -> IntToNat.nat_datatype::cs) css
    let css'' = PropagateNot.propagateAllNots css'
    let css''' = EliminateSelectors.eliminateAllSelectors css''
    List.map preambulize css'''

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
