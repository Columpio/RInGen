module FLispy.ParseExtension
open FLispy.Operations
open FLispy.PropagateNot
open FLispy.VarEnv
open FLispy.Typer
open FLispy.ParseToTerms
open FLispy.UnfoldDeclarations

let mapThird f = List.map (fun (v, a, r) -> v, a, f r)

let private apply_with_new_return_arg op sign =
    let retArg, retVar = Operation.generateReturnArgument (IntToNat.sort_list sign)
    fun (vars, assumptions, args) ->
    let expr = Operation.makeApp op args retVar
    (retArg::vars), (expr::assumptions), retVar

let private fallback_apply op (v, a, rs) = v, a, Apply(op, rs)

//let private expr_to_clauses typer env command =
let rec private expr_to_clauses typer env = function
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
            | UserDefinedOperation(_, sign) -> apply_with_new_return_arg op sign
        List.map app args
    | Not e -> expr_to_clauses typer env e |> mapThird Not
    | Or cases -> product typer env cases |> mapThird Or
    | And exprs -> product typer env exprs |> mapThird And
    | Forall _
    | Exists _ -> __unreachable__()
//    | Forall(vars, e) -> mapInsideQuantifier typer env vars e Forall
//    | Exists(vars, e) -> mapInsideQuantifier typer env vars e Exists
    | Hence(cond, body) ->
        let cond = expr_to_clauses typer env cond
        let body = expr_to_clauses typer env body
        collector {
            let! cvars, cassumptions, cretExpr = cond
            let! bvars, bassumptions, bretExpr = body
            return cvars @ bvars, cretExpr :: cassumptions @ bassumptions, bretExpr
        }
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
        let handle_case (pattern, body) =
            let vars = MatchExtensions.getFreeVarsFromPattern typer pattern
            let vars, env = VarEnv.extend env (IntToNat.sorted_var_list vars)
            let pattern = VarEnv.renameVars typer env pattern
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
and private product typer env args =
    let combine2 arg st =
        let arg = expr_to_clauses typer env arg
        collector {
            let! v, a, r = st
            let! v', a', r' = arg
            return v' @ v, a' @ a, r' :: r
        }
    List.foldBack combine2 args [[], [], []]
and private mapInsideQuantifier typer env vars e constructor =
    let vars, env = VarEnv.extend env (IntToNat.sorted_var_list vars)
    expr_to_clauses typer env e
    |> List.map (fun (vars', assumptions, result) -> [], [], constructor(vars, forall vars' (henceOrNot assumptions result)))
//expr_to_clauses typer env command

//let private clauses_expr_to_clauses = expr_to_clauses (fun op _ -> fallback_apply op)
//let private function_expr_to_clauses = expr_to_clauses apply_with_new_return_arg

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
        expr_to_clauses typer env body
        |> List.map handle_clause
    DeclareFun(name, sign, "Bool"), bodies

let private niceAssertion e =
    match e with
    | Not(Forall _ as e) -> e
    | Forall _ as e -> e
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

let private functionToClauses typer = function
    | DeclareConst _
    | SetLogic _
    | CheckSat
    | DeclareSort _ as c -> [[c]]
    | DeclareDatatypes dfs ->
        let names, constrs = List.unzip dfs
        let constrs = constrs |> List.map IntToNat.constructor_list
        [[DeclareDatatypes(List.zip names constrs)]]
    | DeclareDatatype(name, cs) -> [[DeclareDatatype(name, IntToNat.constructor_list cs)]]
//    | DeclareConst(name, sort) -> [[relational_declaration name [] (IntToNat.sort sort)]]
    | DeclareFun(name, argSorts, sort) -> [[relational_declaration name (IntToNat.sort_list argSorts) (IntToNat.sort sort)]]
    | DefineFun df
    | DefineFunRec df ->
        let df = IntToNat.definition df
        let dec, bodies = definition_to_clauses typer df
        dec :: bodies |> List.map List.singleton
    | DefineFunsRec dfs ->
        let decs, bodies = List.map (IntToNat.definition >> definition_to_clauses typer) dfs |> List.unzip
        decs @ List.concat bodies |> List.map List.singleton
    | Assert query ->
        let Qs, env, query = TakeOutQuantifiers.takeOutQuantifiers typer query
        expr_to_clauses typer env query
        |> List.map (fun (vars, assumptions, body) -> Assert(hence (Not body :: assumptions) falsee |> forall vars |> Qs))
        |> List.singleton
    | c -> failwithf "Can't obtain clauses from: %O" c

let private functionCommandsToClausesSets cs = typerMap functionToClauses cs |> List.concat |> List.product

let private get_info_unknown = GetInfo ":reason-unknown"
let private preambulize cs =
    Diseq.preambula @ cs @ [CheckSat; get_info_unknown]

let functionsToClauses ps =
    let cs = ps |> parseToTerms //|> unfoldDeclarations
    let cs', asserts = collectAsserts cs
    let cs'' = cs' @ List.map Assert asserts // [Assert (And asserts)]
    seq {
        for cs in functionCommandsToClausesSets cs'' do
            let cs''' = PropagateNot.propagateAllNots cs
            yield preambulize cs'''
    } |> List.ofSeq

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
