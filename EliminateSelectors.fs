module FLispy.EliminateSelectors
open FLispy
open FLispy.Operations
open Typer

let private relativizeSelectorName name = Operations.gensymp name

let private generateSelectors typer adtSort constructors selectorsMap =
    // car(x, r) <- x = cons(r, a)
    let generateSelector constructorOp selectorsMap (selectorIndex, (selectorName, selectorType)) =
        let relselectorName = relativizeSelectorName selectorName
        let relselectorOp = ElementaryOperation(relselectorName, [selectorType; adtSort])
        let decl = DeclareFun(relselectorName, [selectorType; adtSort], "Bool")
        let adtArg = Operations.gensym (), adtSort
        let constrArgs = Operations.Operation.generateArguments constructorOp
        let retArg = List.item selectorIndex constrArgs
        let body = Assert(Operations.forall (adtArg::constrArgs)
                              (Operations.hence [Operations.equal (Ident adtArg) (Apply(constructorOp, List.map Ident constrArgs))]
                                   (Apply(relselectorOp, List.map Ident [retArg; adtArg]))))
        [decl; body], Map.add selectorName relselectorOp selectorsMap
    let generateSelectorForConstructor selectorsMap (constructorName, selectorsWithTypes) =
        let constructorOp = Map.find constructorName typer
        let comms, selectorsMap =
            selectorsWithTypes
            |> List.indexed
            |> List.mapFold (generateSelector constructorOp) selectorsMap
        List.concat comms, selectorsMap
    let comms, selectorsMap = List.mapFold generateSelectorForConstructor selectorsMap constructors
    List.concat comms, selectorsMap

let rec private eliminateSelectorsExprRec typer selectors assumptions vars =
    let eliminateSelectorsExprRecFold (assumptions, vars) arg =
        let res, assumptions, vars = eliminateSelectorsExprRec typer selectors assumptions vars arg
        res, (assumptions, vars)
    let eliminateSelectorsListExpr = List.mapFold eliminateSelectorsExprRecFold (assumptions, vars)
    function
    | Constant _
    | Ident _ as e -> e, assumptions, vars
    | Apply(op, args) ->
        let args, (assumptions, vars) = eliminateSelectorsListExpr args
        match Map.tryFind (Operation.opName op) selectors with
        | Some selector ->
            let retArg, retVar = Operation.generateReturnArgumentOfOperation selector
            retVar, Apply(selector, retVar::args)::assumptions, retArg::vars
        | None -> Apply(op, args), assumptions, vars
    | Hence(And es, b) ->
        let es, (assumptions, vars) = eliminateSelectorsListExpr es
        let b, assumptionsB, varsB = eliminateSelectorsExprRec typer selectors (es @ assumptions) vars b
        b, assumptionsB, varsB
    | Hence(a, b) ->
        let a, assumptionsA, varsA = eliminateSelectorsExprRec typer selectors assumptions vars a
        let b, assumptionsB, varsB = eliminateSelectorsExprRec typer selectors (a::assumptionsA) varsA b
        b, assumptionsB, varsB
    | Or es ->
        let args, (assumptions, vars) = eliminateSelectorsListExpr es
        Or args, assumptions, vars
    | And es ->
        let args, (assumptions, vars) = eliminateSelectorsListExpr es
        And args, assumptions, vars
    | Forall(vars', body) -> // A x. head x = a -> A x. A r. (head x r -> r = a) <-> A x. A r. (r = head x -> r = a)
        let body, assumptions', vars' = eliminateSelectorsExprRec typer selectors [] vars' body
        Forall(vars', hence assumptions' body), assumptions, vars
    | Exists(vars', body) -> // E x. head x = a -> E x. A r. (head x r -> r = a)
        let body, assumptions'', vars'' = eliminateSelectorsExprRec typer selectors [] [] body
        Exists(vars', forall vars'' (hence assumptions'' body)), assumptions, vars
    | Not e ->
        let e, assumptions, vars = eliminateSelectorsExprRec typer selectors assumptions vars e
        Not e, assumptions, vars
    | Ite(i, t, e) ->
        let i, assumptions, vars = eliminateSelectorsExprRec typer selectors assumptions vars i
        let t, assumptions, vars = eliminateSelectorsExprRec typer selectors assumptions vars t
        let e, assumptions, vars = eliminateSelectorsExprRec typer selectors assumptions vars e
        Ite(i, t, e), assumptions, vars
//    | Match(t, cases) ->
//        let handle_case (pattern, body) =
//            let vars = MatchExtensions.getFreeVarsFromPattern typer pattern
//            let vars, env = VarEnv.extend env (Typer.sorted_var_list ts vars)
//            let pattern = VarEnv.renameVars ts env pattern
//            expr_to_clauses ts env body
//            |> List.map (fun (vars', assumptions, body) -> pattern, vars @ vars', assumptions, body)
//        let t = expr_to_clauses ts env t
//        let cases = List.collect handle_case cases
//        collector {
//            let! tvars, tassumptions, tretExpr = t
//            let! pattern, brvars, brassumptions, brretExpr = cases
//            let pat_match = equal tretExpr pattern
//            return tvars @ brvars, pat_match :: tassumptions @ brassumptions, brretExpr
//        }
    | Let(bindings, body) -> // let x = e in p(x) <-> p(e) <-> E x. (x = e /\ p(x))
        // let x = head a
        //     y = head x
        // in x <> head y
        // A r1 r2 r3. let x = r1, y = r2 in head a r1 /\ head x r2 /\ head y r3 -> x <> r3
        let handle_binding (assumptions, vars) (var, body) =
            let body, assumptions, vars = eliminateSelectorsExprRec typer selectors assumptions vars body
            (var, body), (assumptions, vars)
        let bindings, (letAssumptions, vars) = List.mapFold handle_binding ([], vars) bindings
        let body, letAssumptions, vars = eliminateSelectorsExprRec typer selectors letAssumptions vars body
        Let(bindings, hence letAssumptions body), assumptions, vars
    | _ -> __notImplemented__()

let private eliminateSelectorsExpr typer selectors =
    let eliminateSelectorsExpr vars body =
        let head, body, vars = eliminateSelectorsExprRec typer selectors [] vars body
        forall vars (hence body head)
    function
    | Forall(vars, body) -> eliminateSelectorsExpr vars body
    | Hence _
    | Apply _ as e -> eliminateSelectorsExpr [] e
    | _ -> __notImplemented__()

let private eliminateSelectorsCommand (typer, _) selectors =
    function
    | DeclareConst _
    | GetInfo _
    | CheckSat
    | DeclareFun _
    | DeclareSort _
    | GetModel
    | SetLogic _ as c -> [c], selectors
    | DeclareDatatype(name, cs) as c ->
        let decls, selectors = generateSelectors typer name cs selectors
        c :: decls, selectors
    | DeclareDatatypes dts as c ->
        let decls, selectors = List.mapFold (fun selectors (name, cs) -> generateSelectors typer name cs selectors) selectors dts
        c :: List.concat decls, selectors
    | Assert e -> [Assert <| eliminateSelectorsExpr typer selectors e], selectors
    | DefineFun _
    | DefineFunRec _
    | DefineFunsRec _ -> __unreachable__()

let private eliminateAllSelectorsInBenchmark cs = cs |> typerFold eliminateSelectorsCommand Map.empty |> List.concat

let eliminateAllSelectors css = List.map eliminateAllSelectorsInBenchmark css