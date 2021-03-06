module RInGen.SMTcode
open System.Runtime.CompilerServices
open RInGen.Operations
open RInGen.Typer
open Relativization
open SubstituteOperations

module private RemoveVariableOverlapping =
    let private mapOrDefault sortMap s =
        match Map.tryFind s sortMap with
        | Some s -> s
        | None -> s
    let private mapSortedVar nameMap sortMap (v, s) = mapOrDefault nameMap v, mapOrDefault sortMap s
    let private mapSortedVars nameMap sortMap vs = List.map (mapSortedVar nameMap sortMap) vs
    let private addSortedVar (nameMap, sortMap) (v, s) =
        let newV = IdentGenerator.gensymp v
        (newV, mapOrDefault sortMap s), (Map.add v newV nameMap, sortMap)
    let private addSortedVars nameMap sortMap vs = List.mapFold addSortedVar (nameMap, sortMap) vs
    let private extendEnvironment (typenv, nameMap, sortMap) vars =
        let vars, (nameMap, sortMap) = addSortedVars nameMap sortMap vars
        let vars, typenv = VarEnv.extend typenv vars
        vars, (typenv, nameMap, sortMap)
    let private extendEnvironmentSingle (typenv, nameMap, sortMap) v =
        let v, (nameMap, sortMap) = addSortedVar (nameMap, sortMap) v
        let v, typenv = VarEnv.extendOne typenv v
        v, (typenv, nameMap, sortMap)
    let private readVar (typenv, nameMap, sortMap) v =
        let v = mapSortedVar nameMap sortMap v
        VarEnv.get typenv v
    let private mapOp (_, nameMap, sortMap) = function
        | ElementaryOperation(name, ss, s) -> ElementaryOperation(mapOrDefault nameMap name, List.map (mapOrDefault sortMap) ss, mapOrDefault sortMap s)
        | UserDefinedOperation(name, ss, s) -> UserDefinedOperation(mapOrDefault nameMap name, List.map (mapOrDefault sortMap) ss, mapOrDefault sortMap s)
    let rec private mapPattern (((typer : Typer, _), nameMap, sortMap) as te) = function
        | Apply(op, ts) ->
            let ts = List.map (mapPattern te) ts
            Apply(mapOp te op, ts)
        | Ident(v, s) as t ->
            let (v, s) = mapSortedVar nameMap sortMap (v, s)
            if typer.containsKey v then Ident(v, s) else t
        | t -> t


    let rec private cleanExpr te = function
        | Apply(op, ts) ->
            let ts = List.map (cleanExpr te) ts
            Apply(mapOp te op, ts)
        | Forall(vars, body) ->
            let vars, te = extendEnvironment te vars
            let body = cleanExpr te body
            Forall(vars, body)
        | Exists(vars, body) ->
            let vars, te = extendEnvironment te vars
            let body = cleanExpr te body
            Exists(vars, body)
        | And fs ->
            let fs = List.map (cleanExpr te) fs
            ande fs
        | Or fs ->
            let fs = List.map (cleanExpr te) fs
            ore fs
        | Hence(i, t) ->
            let i = cleanExpr te i
            let t = cleanExpr te t
            Hence(i, t)
        | Not t ->
            let t = cleanExpr te t
            note t
        | BoolConst _
        | Number _ as t -> t
        | Ident(v, s) -> readVar te (v, s) |> Ident
        | Ite(i, t, e) ->
            let i = cleanExpr te i
            let t = cleanExpr te t
            let e = cleanExpr te e
            Ite(i, t, e)
        | Let(assignments, body) ->
            let handleAssignment te (v, e) =
                let e = cleanExpr te e
                let v', te' = extendEnvironmentSingle te v
                (v', e), te'
            let assignments, te = List.mapFold handleAssignment te assignments
            let body = cleanExpr te body
            Let(assignments, body)
        | Match(e, cases) ->
            let e = cleanExpr te e
            let handleUnification ((typer, _), _, _ as te) (pattern, body) =
                let pattern = mapPattern te pattern
                let freeVars = ADTExtensions.getFreeVarsFromPattern typer pattern
                let _, te = extendEnvironment te freeVars
                let pattern = cleanExpr te pattern
                let body = cleanExpr te body
                (pattern, body)
            let cases = List.map (handleUnification te) cases
            Match(e, cases)

    let private cleanFuncDef (typer, nameMap, sortMap) (name, vars, sort, body) =
        let vars, (nameMap, sortMap) = addSortedVars nameMap sortMap vars
        let te = VarEnv.create typer vars
        name, vars, sort, cleanExpr (te, nameMap, sortMap) body

    let private cleanCommand ((typr, nameMap, sortMap) as typer) = function
        | Command _ as c -> c
        | Definition(DefineFun df) -> cleanFuncDef typer df |> DefineFun |> Definition
        | Definition(DefineFunRec df) -> cleanFuncDef typer df |> DefineFunRec |> Definition
        | Definition(DefineFunsRec dfs) -> dfs |> List.map (cleanFuncDef typer) |> DefineFunsRec |> Definition
        | Assert f -> f |> cleanExpr ((typr, VarEnv.empty), nameMap, sortMap) |> Assert

    let private substWithNameMap nameMap s = Map.find s nameMap
    let rec private substWithSortMap sortMap s =
        match Map.tryFind s sortMap with
        | Some s -> s
        | None ->
            match s with
            | PrimitiveSort _ -> s
            | ArraySort(s1, s2) -> ArraySort(substWithSortMap sortMap s1, substWithSortMap sortMap s2)
    let private substWithNameMapList nameMap = List.map (substWithNameMap nameMap)
    let private substWithSortMapList sortMap = List.map (substWithSortMap sortMap)
    let private substWithNameMapPairList nameMap sortMap =  (fun (a, b) -> substWithNameMap nameMap a, substWithSortMap sortMap b)
    let private prepareDefinition (nameMap, sortMap) (name, args, retSort, body) =
        let newName = IdentGenerator.gensymp name
        let nameMap = Map.add name newName nameMap
        let args = List.map (fun (v, s) -> (v, substWithSortMap sortMap s)) args
        (newName, args, substWithSortMap sortMap retSort, body), (nameMap, sortMap)

    let private addDatatypeSorts (nameMap, sortMap) (name, cs) =
        let newName = IdentGenerator.gensymsort name
        (nameMap, Map.add name newName sortMap)
    let private substDatatypeSorts (nameMap, sortMap) (name, cs) =
        let mapSelector (nameMap, sortMap) (sel, sort) =
            let newSel = IdentGenerator.gensymp sel
            (newSel, substWithSortMap sortMap sort), (Map.add sel newSel nameMap, sortMap)
        let mapConstr (nameMap, sortMap) (constr, selectors) =
            let newConstr = IdentGenerator.gensymp constr
            let nameMap = Map.add constr newConstr nameMap
            let selectors, (nameMap, sortMap) = List.mapFold mapSelector (nameMap, sortMap) selectors
            (newConstr, selectors), (nameMap, sortMap)
        let cs, (nameMap, sortMap) = List.mapFold mapConstr (nameMap, sortMap) cs
        (substWithSortMap sortMap name, cs), (nameMap, sortMap)

    let private prepareCommand nameMap sortMap = function
        | Command(DeclareConst(name, sort)) ->
            let newName = IdentGenerator.gensymp name
            Map.add name newName nameMap, sortMap, Command(DeclareConst(newName, substWithSortMap sortMap sort))
        | Command(DeclareFun(name, argTypes, sort)) ->
            let newName = IdentGenerator.gensymp name
            Map.add name newName nameMap, sortMap, Command(DeclareFun(newName, substWithSortMapList sortMap argTypes, substWithSortMap sortMap sort))
        | Command(DeclareSort name) ->
            let newName = IdentGenerator.gensymsort name
            nameMap, Map.add name newName sortMap, Command(DeclareSort newName)
        | Definition(DefineFunRec df) ->
            let df, (nameMap, sortMap) = prepareDefinition (nameMap, sortMap) df
            nameMap, sortMap, Definition(DefineFunRec df)
        | Definition(DefineFun df) ->
            let df, (nameMap, sortMap) = prepareDefinition (nameMap, sortMap) df
            nameMap, sortMap, Definition(DefineFun df)
        | Definition(DefineFunsRec dfs) ->
            let dfs, (nameMap, sortMap) = List.mapFold prepareDefinition (nameMap, sortMap) dfs
            nameMap, sortMap, Definition(DefineFunsRec dfs)
        | Command(DeclareDatatype(name, cs)) ->
            let nameMap, sortMap = addDatatypeSorts (nameMap, sortMap) (name, cs)
            let (name, cs), (nameMap, sortMap) = substDatatypeSorts (nameMap, sortMap) (name, cs)
            nameMap, sortMap, Command(DeclareDatatype(name, cs))
        | Command(DeclareDatatypes dts) ->
            let nameMap, sortMap = dts |> List.fold addDatatypeSorts (nameMap, sortMap)
            let dts, (nameMap, sortMap) = List.mapFold substDatatypeSorts (nameMap, sortMap) dts
            nameMap, sortMap, Command(DeclareDatatypes dts)
        | c -> nameMap, sortMap, c

    let private renameIdentsInCommand (typer, nameMap, sortMap) c =
        let nameMap, sortMap, c = prepareCommand nameMap sortMap c
        let typer = Typer.interpretCommand typer c
        cleanCommand (typer, nameMap, sortMap) c, (typer, nameMap, sortMap)

    let removeVariableOverlapping = List.mapFold renameIdentsInCommand (Typer.empty, Map.empty, Map.empty) >> fst

module private DefinitionsToDeclarations =
    let private aand = function
        | [t] -> t
        | ts -> AAnd ts

    let rec private atomToTerm = function
        | AApply(op, ts) -> TApply(op, ts)
        | Distinct(t, t2) when t2 = truet -> TApply(Map.find (symbol "not") elementaryOperations, [t])
        | ANot t -> TApply(Map.find (symbol "not") elementaryOperations, [atomToTerm t])
        | t -> failwithf "Can't obtain term from atom: %O" t

    let rec private exprToTerm atomsAreTerms = function
        | Ident(name, sort) -> TIdent(name, sort)
        | BoolConst _ as e -> e |> toString |> symbol |> TConst
        | Or es -> TApply(Map.find (symbol "or") elementaryOperations, exprsToTerms atomsAreTerms es)
        | And es -> TApply(Map.find (symbol "and") elementaryOperations, exprsToTerms atomsAreTerms es)
        | Not e -> e |> exprToAtom atomsAreTerms |> nota |> atomToTerm
        | Hence(a, b) -> TApply(Map.find (symbol "=>") elementaryOperations, [exprToTerm atomsAreTerms a; exprToTerm atomsAreTerms b])
        | Apply(ElementaryOperation _ as op, ts) -> TApply(op, exprsToTerms atomsAreTerms ts)
        | Apply(UserDefinedOperation _ as op, ts) -> TApply(op, exprsToTerms atomsAreTerms ts)
        | Number n -> n |> toString |> symbol |> TConst //TODO: IntToNat
        | t -> failwithf "Can't obtain term from expr: %O" t
    and private exprsToTerms atomsAreTerms = List.map (exprToTerm atomsAreTerms)

    and private exprToAtoms atomsAreTerms = function
        | Not (Not t) -> exprToAtoms atomsAreTerms t
        | Not t -> t |> exprToAtom atomsAreTerms |> nota |> List.singleton
        | Ident(name, s) when s = boolSort -> [AApply(identToUserOp name s, [])]
        | BoolConst true -> [Top]
        | BoolConst false -> [Bot]
        | Apply(UserDefinedOperation(_, _, s) as op, ts) when s = boolSort ->
            if atomsAreTerms
                then [Equal(TApply(op, exprsToTerms atomsAreTerms ts), truet)]
                else [AApply(op, exprsToTerms atomsAreTerms ts)]
        | And ts -> List.collect (exprToAtoms atomsAreTerms) ts
        | Hence(a, b) -> [AHence(aand <| exprToAtoms atomsAreTerms a, aand <| exprToAtoms atomsAreTerms b)]
        | Or ts -> ts |> List.map (exprToAtoms atomsAreTerms >> aand) |> AOr |> List.singleton
        | Apply(ElementaryOperation("=", _, _), [t1; t2]) -> [Equal(exprToTerm atomsAreTerms t1, exprToTerm atomsAreTerms t2)]
        | Apply(ElementaryOperation("distinct", _, _), [t1; t2]) -> [distinct (exprToTerm atomsAreTerms t1) (exprToTerm atomsAreTerms t2)]
        | Apply(ElementaryOperation(_, _, s) as op, ts) when s = boolSort  -> [AApply(op, exprsToTerms atomsAreTerms ts)]
        | t -> failwithf "Can't obtain atom from expr: %O" t

    and private exprToAtom atomsAreTerms t =
        match exprToAtoms atomsAreTerms t with
        | [t] -> t
        | ts -> AAnd ts

    let private functionExprToTerm = exprToTerm true

    type private syntaxRule =
        | AllRule of sorted_var list * syntaxRule
        | ExRule of sorted_var list * syntaxRule
        | StableAllRule of sorted_var list * syntaxRule
        | BRule of atom list * atom
    let rec private syntaxRuleToRule = function
        | AllRule(vars, body)
        | StableAllRule(vars, body) -> ForallRule(vars, syntaxRuleToRule body)
        | ExRule(vars, body) -> ExistsRule(vars, syntaxRuleToRule body)
        | BRule(p, c) -> BaseRule(p, c)
    let rec private forallrule = function
        | [] -> id
        | vars -> function
            | AllRule(vars', body) -> forallrule (vars @ vars') body
            | body -> AllRule(vars, body)
    let rec private existsrule = function
        | [] -> id
        | vars -> function
            | ExRule(vars', body) -> existsrule (vars @ vars') body
            | body -> ExRule(vars, body)
    let rec private stableallrule = function
        | [] -> id
        | vars -> function
            | StableAllRule(vars', body) -> stableallrule (vars @ vars') body
            | body -> StableAllRule(vars, body)
    let private emptyQuantifier = id
    let rec private combineQuantifiers q1 q2 = q1 << q2
    let private negateQuantifiers q =
        let rec negate = function
            | AllRule(vars, body) -> combineQuantifiers (existsrule vars) (negate body)
            | ExRule(vars, body) -> combineQuantifiers (forallrule vars) (negate body)
            | StableAllRule(vars, body) -> combineQuantifiers (stableallrule vars) (negate body)
            | BRule _ -> emptyQuantifier
        negate (q (BRule([], Bot)))

    let rec private toRuleProduct vars args =
        let combine2 arg st =
            let arg = exprToRule vars arg
            collector {
                let! v, a, r = st
                let! v', a', r' = arg
                return combineQuantifiers v' v, a' @ a, r' :: r
            }
        List.foldBack combine2 args [emptyQuantifier, [], []]
    and private toRuleHandleProduct te constructor ts =
        collector {
            let! vs, cs, rs = toRuleProduct te ts
            return vs, cs, constructor rs
        }
    and private exprToRule (typer : Typer, _ as te) = function
        | Apply(op, ts) -> toRuleHandleProduct te (fun ts -> Apply(op, ts)) ts
        | Ident _
        | Number _
        | BoolConst _ as e -> [emptyQuantifier, [], e]
        | And fs -> toRuleHandleProduct te ande fs
        | Or fs -> toRuleHandleProduct te ore fs
        | Hence(a, b) ->
            collector {
                let! avs, acs, ar = exprToRule te a
                let! bvs, bcs, br = exprToRule te b
                return combineQuantifiers (negateQuantifiers avs) bvs, acs @ bcs, Hence(ar, br)
            }
        | Not e ->
            collector {
                let! vs, cs, r = exprToRule te e
                return negateQuantifiers vs, cs, note r
            }
        | Forall(vars, body) ->
            let te = VarEnv.replace te vars
            collector {
                let! bodyVars, bodyConditions, bodyResult = exprToRule te body
                return combineQuantifiers (forallrule vars) bodyVars, bodyConditions, bodyResult
            }
        | Exists(vars, body) ->
            let te = VarEnv.replace te vars
            collector {
                let! bodyVars, bodyConditions, bodyResult = exprToRule te body
                return combineQuantifiers (existsrule vars) bodyVars, bodyConditions, bodyResult
            }
        | Let(assignments, body) ->
            let handleAssignment te (v, expr) =
                let te = VarEnv.replaceOne te v
                collector {
                    let! exprvs, exprcs, expr = exprToRule te expr
                    return combineQuantifiers (stableallrule [v]) exprvs, (Equal(TIdent v, functionExprToTerm expr)::exprcs)
                }, te
            let assignments, te = List.mapFold handleAssignment te assignments  // [[even; odd]; [0mod3; 1mod3; 2mod3]]
            collector {
                let! assignments = List.product assignments                     // [[even; 0mod3]; [even; 1mod3]; ...]
                let vars, conds = List.unzip assignments
                let vars = List.reduceBack combineQuantifiers vars
                let conds = List.concat conds
                let! bodyvs, bodycs, body = exprToRule te body
                return combineQuantifiers vars bodyvs, conds @ bodycs, body
            }
        | Match(expr, cases) ->
            let handle_case patterns (pattern, body) =
                let varsList = ADTExtensions.getFreeVarsFromPattern typer pattern
                let te = VarEnv.replace te varsList
                let body =
                    exprToRule te body
                    |> List.map (fun (vars', assumptions, body) -> pattern, patterns, combineQuantifiers (stableallrule varsList) vars', assumptions, body)
                body, pattern::patterns
            let expr = exprToRule te expr
            let cases = List.mapFold handle_case [] cases |> fst |> List.concat
            collector {
                let! tvars, tassumptions, tretExpr = expr
                let tretExpr = functionExprToTerm tretExpr
                let! pattern, patterns, brvars, brassumptions, brretExpr = cases
                let! pvars, pattern_match = ADTExtensions.patternsToConstraints typer patterns pattern (fun pat -> Equal(tretExpr, functionExprToTerm pat))
                return combineQuantifiers (stableallrule pvars) (combineQuantifiers tvars brvars), pattern_match :: tassumptions @ brassumptions, brretExpr
            }
        | Ite(i, t, e) ->
            collector {
                let! ivs, ics, ir = exprToRule te i
                let! tvs, tcs, tr = exprToRule te t
                let! evs, ecs, er = exprToRule te e
                let thenBranch = combineQuantifiers ivs tvs, exprToAtoms true ir @ ics @ tcs, tr
                let elseBranch = combineQuantifiers ivs evs, exprToAtoms true (note ir) @ ics @ ecs, er
                return! [thenBranch; elseBranch]
            }

    let private definitionToDeclaration (name, vars, sort, _) =
        let argTypes = List.map snd vars
        let decl = DeclareFun(name, argTypes, sort)
        OriginalCommand decl

    let private defineOperationName = symbol "*define*"
    let private defineOperation call body = Operation.makeElementaryOperationFromSorts defineOperationName [typeOfTerm call; typeOfTerm body] boolSort
    let (|DefineOperation|_|) = function
        | AApply(ElementaryOperation(name, [_; _], s), [call; bodyResult]) when name = defineOperationName && s = boolSort -> Some (call, bodyResult)
        | _ -> None
    let private connectFunctionCallWithBody call bodyResult =
        let bodyResult = functionExprToTerm bodyResult
        AApply(defineOperation call bodyResult, [call; bodyResult])
    let private connectFunctionNameWithBody userFuncOp args bodyResult = connectFunctionCallWithBody (TApply(userFuncOp, List.map TIdent args)) bodyResult

    let private finalRule vars qbvars qhvars conds result =
        combineQuantifiers (forallrule vars) (combineQuantifiers (negateQuantifiers qbvars) qhvars) (BRule(conds, result))
        |> syntaxRuleToRule

    let private definitionToAssertion typer (name, vars, sort, body) =
        let userFuncOp = Operation.makeUserOperationFromVars name vars sort
        collector {
            let! bodyVars, bodyConditions, bodyResult = exprToRule (VarEnv.create typer vars) body
            let body = finalRule vars emptyQuantifier bodyVars bodyConditions (connectFunctionNameWithBody userFuncOp vars bodyResult)
            return TransformedCommand body
        }

    let private expressionToDeclarations assertsToQueries typer =
        let rec eatCondition = function
            | And cs -> List.collect eatCondition cs
            | c -> [c]
        let rec eat vars conds = function
            | Forall(vars', body) -> eat (vars @ vars') conds body
            | Or es -> eat vars conds (hence (List.map note es) falsee)
            | Hence(cond, body) -> eat vars (eatCondition cond @ conds) body
            | And es -> List.collect (eat vars conds) es
//            | Apply(op, [app; body]) when op = equal_op boolSort ->
//                let vars, body =
//                    match body with
//                    | Forall(varsBody, body) -> vars @ varsBody, body
//                    | _ -> vars, body
//                let te = VarEnv.create typer vars
//                collector {
//                    let! bodyVars, bodyConditions, bodyResult = exprToRule te body
//                    let bodyResult = exprToAtoms bodyResult
//                    let! appVars, appConditions, appResult = exprToRule te app
//                    let r = finalRule vars bodyVars appVars (bodyResult @ bodyConditions @ appConditions) (getAppResult appResult)
//                    return TransformedCommand r
//                }
//            | Apply(ElementaryOperation("=", _, _), [app; body]) ->
//                let te = VarEnv.create typer vars
//                collector {
//                    let! bodyVars, bodyConditions, bodyResult = exprToRule te body
//                    let! appVars, appConditions, appResult = exprToRule te app
//                    let r = finalRule vars bodyVars appVars (bodyConditions @ appConditions) (connectFunctionCallWithBody (exprToTerm appResult) bodyResult)
//                    return TransformedCommand r
//                }
            | app ->
                let te = VarEnv.create typer vars
                collector {
                    let! bodyVars, bodyConditions, bodyResult = toRuleProduct te conds
                    let! appVars, appConditions, appResult = exprToRule te app
                    let bodyAddition, head = if assertsToQueries then exprToAtoms assertsToQueries (note appResult), Bot else [], exprToAtom assertsToQueries appResult
                    let r = finalRule vars bodyVars appVars (bodyAddition @ List.collect (exprToAtoms assertsToQueries) bodyResult @ bodyConditions @ appConditions) head
                    return TransformedCommand r
                }
        eat [] []

    let rec private defineCommandToDeclarations assertsToQueries typer = function
        | Definition(DefineFun df)
        | Definition(DefineFunRec df) -> definitionToDeclaration df :: definitionToAssertion typer df
        | Definition(DefineFunsRec dfs) -> List.map definitionToDeclaration dfs @ List.collect (definitionToAssertion typer) dfs
        | Assert e -> expressionToDeclarations assertsToQueries typer e
        | Command c -> [OriginalCommand c]

    let definesToDeclarations assertsToQueries commands =
        Typer.typerFold (defineCommandToDeclarations assertsToQueries) commands |> List.concat

module private TIPFixes =
    let rec private invertMatchesInExpr = function
        | Match(e, pats) ->
            let e = invertMatchesInExpr e
            let pats = List.map (fun (p, b) -> p, invertMatchesInExpr b) pats
            Match(e, List.rev pats)
        | Number _
        | BoolConst _
        | Ident _ as e -> e
        | Apply(op, es) -> Apply(op, invertMatchesInExprList es)
        | Let(defs, body) ->
            let defs = List.map (fun (v, e) -> v, invertMatchesInExpr e) defs
            Let(defs, invertMatchesInExpr body)
        | Ite(i, t, e) -> Ite(invertMatchesInExpr i, invertMatchesInExpr t, invertMatchesInExpr e)
        | And es -> es |> invertMatchesInExprList |> ande
        | Or es -> es |> invertMatchesInExprList |> ore
        | Not e -> e |> invertMatchesInExpr |> note
        | Hence(a, b) -> Hence(invertMatchesInExpr a, invertMatchesInExpr b)
        | Forall(vars, body) -> Forall(vars, invertMatchesInExpr body)
        | Exists(vars, body) -> Exists(vars, invertMatchesInExpr body)
    and private invertMatchesInExprList = List.map invertMatchesInExpr

    let private invertMatchesInDef (name, args, ret, body) = name, args, ret, invertMatchesInExpr body
    let private invertMatchesInDefinition = function
        | DefineFun df -> df |> invertMatchesInDef |> DefineFun
        | DefineFunRec df -> df |> invertMatchesInDef |> DefineFunRec
        | DefineFunsRec dfs -> dfs |> List.map invertMatchesInDef |> DefineFunsRec

    let private invertMatches = function
        | Assert e -> e |> invertMatchesInExpr |> Assert
        | Command _ as c -> c
        | Definition df -> df |> invertMatchesInDefinition |> Definition

    let applyTIPfix commands =
        let commands = List.map (function Assert(Not(Forall(vars, body))) -> Assert(Forall(vars, body)) | c -> c) commands
        List.map invertMatches commands

module private RelativizeSymbols =
    open DefinitionsToDeclarations
    let private addNewSymbolsToRelativize rels = function
        | OriginalCommand(DeclareFun(name, args, ret)) ->
            let op = Operation.makeUserOperationFromSorts name args ret
            addShouldRelativize op (Relativization.relativizeOperation op) rels
        | _ -> rels

    let private assertIsFunction name args ret =
        let op = Operation.makeUserOperationFromSorts name args ret |> relativizeOperation
        let args = args |> List.map (fun s -> IdentGenerator.gensym (), s)
        let ret = IdentGenerator.gensym (), ret
        aerule args [ret] [] (relapply op (List.map TIdent args) (TIdent ret))

    let private relativizeDeclarations = function
        | OriginalCommand(DeclareFun(name, args, ret)) ->
            let decl = reldeclare name args ret
//            let assertNonEmpty = TransformedCommand <| assertIsFunction name args ret
            [OriginalCommand decl]
        | TransformedCommand(Rule(vars, c::cs, DefineOperation(call, bodyResult))) -> [rule vars (Equal(call, bodyResult)::cs) c |> TransformedCommand]
        | c -> [c]

    let relativizeSingleCommand rels command =
        let rels = addNewSymbolsToRelativize rels command
        let relativizer = SubstituteOperations(rels)
        let command = relativizer.SubstituteOperationsWithRelations(command)
        command, rels

    let relativizeSymbols commands =
        let commands, _ = List.mapFold relativizeSingleCommand Map.empty commands
        List.collect relativizeDeclarations commands

module DatatypesToSorts =
    let private sortDeclaration (name, _) = DeclareSort name

    let private constrDeclarations (typename, constructors) =
        let parse_constructor (name, args) = DeclareFun(name, List.map snd args, typename)
        List.map parse_constructor constructors

    let private generateConstructorDeclarations = function
        | OriginalCommand(DeclareDatatype(name, constrs)) ->
            sortDeclaration (name, constrs) :: constrDeclarations (name, constrs)
            |> List.map OriginalCommand
        | OriginalCommand(DeclareDatatypes dts) ->
            List.map sortDeclaration dts @ List.collect constrDeclarations dts
            |> List.map OriginalCommand
        | OriginalCommand(DeclareConst(name, sort)) -> DeclareFun(name, [], sort) |> OriginalCommand |> List.singleton
        | c -> [c]

    let datatypesToSorts commands =
        List.collect generateConstructorDeclarations commands

type MapSorts<'acc>(mapSort : 'acc -> sort -> sort * 'acc) =
    let mapSorts = List.mapFold mapSort

    let mapSortedVar arraySorts (name, sort) =
        let sort, arraySorts = mapSort arraySorts sort
        (name, sort), arraySorts

    let mapSortedVars = List.mapFold mapSortedVar

    let mapOp arraySorts =
        let mapOp constr name args ret =
            let args, arraySorts = mapSorts arraySorts args
            let ret, arraySorts = mapSort arraySorts ret
            constr(name, args, ret), arraySorts
        function
        | UserDefinedOperation(name, args, ret) -> mapOp UserDefinedOperation name args ret
        | ElementaryOperation(name, args, ret) -> mapOp ElementaryOperation name args ret

    let rec mapTerm arraySorts = function
        | TConst _ as c -> c, arraySorts
        | TIdent(name, sort) ->
            let sort, arraySorts = mapSort arraySorts sort
            TIdent(name, sort), arraySorts
        | TApply(op, ts) ->
            let op, arraySorts = mapOp arraySorts op
            let ts, arraySorts = mapTerms arraySorts ts
            TApply(op, ts), arraySorts
    and mapTerms = List.mapFold mapTerm

    let rec mapAtom arraySorts = function
        | Top | Bot as a -> a, arraySorts
        | Equal(t1, t2) ->
            let t1, arraySorts = mapTerm arraySorts t1
            let t2, arraySorts = mapTerm arraySorts t2
            Equal(t1, t2), arraySorts
        | Distinct(t1, t2) ->
            let t1, arraySorts = mapTerm arraySorts t1
            let t2, arraySorts = mapTerm arraySorts t2
            Distinct(t1, t2), arraySorts
        | AApply(op, ts) ->
            let op, arraySorts = mapOp arraySorts op
            let ts, arraySorts = mapTerms arraySorts ts
            AApply(op, ts), arraySorts
        | AAnd xs ->
            let xs, arraySorts = mapAtoms arraySorts xs
            AAnd xs, arraySorts
        | AOr xs ->
            let xs, arraySorts = mapAtoms arraySorts xs
            AOr xs, arraySorts
        | AHence(a, b) ->
            let a, arraySorts = mapAtom arraySorts a
            let b, arraySorts = mapAtom arraySorts b
            AHence(a, b), arraySorts
        | ANot a ->
            let a, arraySorts = mapAtom arraySorts a
            ANot a, arraySorts
    and mapAtoms = List.mapFold mapAtom

    let mapDatatype arraySorts (name, constrs) =
        let constrs, arraySorts =
            List.mapFold (fun arraySorts (name, vars) -> let vars, arraySorts = mapSortedVars arraySorts vars in (name, vars), arraySorts) arraySorts constrs
        (name, constrs), arraySorts

    let mapArraySortsInOrigCommand arraySorts = function
        | DeclareFun(name, argSorts, retSort) ->
            let argSorts, arraySorts = mapSorts arraySorts argSorts
            let retSort, arraySorts = mapSort arraySorts retSort
            DeclareFun(name, argSorts, retSort), arraySorts
        | DeclareDatatype(name, constrs) ->
            let (name, constrs), arraySorts = mapDatatype arraySorts (name, constrs)
            DeclareDatatype(name, constrs), arraySorts
        | DeclareDatatypes dts ->
            let dts, arraySorts = List.mapFold mapDatatype arraySorts dts
            DeclareDatatypes dts, arraySorts
        | DeclareConst(name, sort) ->
            let retSort, arraySorts = mapSort arraySorts sort
            DeclareConst(name, retSort), arraySorts
        | c -> c, arraySorts

    let rec mapRule arraySorts = function
        | ForallRule(vars, body) ->
            let vars, arraySorts = mapSortedVars arraySorts vars
            let body, arraySorts = mapRule arraySorts body
            ForallRule(vars, body), arraySorts
        | ExistsRule(vars, body) ->
            let vars, arraySorts = mapSortedVars arraySorts vars
            let body, arraySorts = mapRule arraySorts body
            ExistsRule(vars, body), arraySorts
        | BaseRule(premises, conclusion) ->
            let premises, arraySorts = mapAtoms arraySorts premises
            let conclusion, arraySorts = mapAtom arraySorts conclusion
            BaseRule(premises, conclusion), arraySorts

    member x.FoldOperation(arraySorts, op) = mapOp arraySorts op

    member x.FoldCommand arraySorts command =
        match command with
        | OriginalCommand c ->
            let c, arraySorts = mapArraySortsInOrigCommand arraySorts c
            OriginalCommand c, arraySorts
        | TransformedCommand r ->
            let r, arraySorts = mapRule arraySorts r
            TransformedCommand r, arraySorts

[<Extension>]
type Utils () =
    [<Extension>]
    static member inline MapCommand(x: MapSorts<unit>, command) = x.FoldCommand () command |> fst
    [<Extension>]
    static member inline MapOperation(x: MapSorts<unit>, op) = x.FoldOperation((), op) |> fst

module private ArrayTransformations =
    let private declareOp = function
        | ElementaryOperation(name, argSorts, retSort) -> DeclareFun(name, argSorts, retSort)
        | UserDefinedOperation(name, argSorts, retSort) -> DeclareFun(name, argSorts, retSort)

    let private generateArraySortName s1 s2 = IdentGenerator.gensyms ("Array" + sortToFlatString s1 + sortToFlatString s2)
    let private generateSelectName newSort = IdentGenerator.gensymp (Symbols.addPrefix "select" newSort)
    let private generateStoreName newSort = IdentGenerator.gensymp (Symbols.addPrefix "store" newSort)

    let private generateSelectOp newSortName newSort indexSort elementSort =
        let selectName = generateSelectName newSortName
        Operation.makeElementaryOperationFromSorts selectName [newSort; indexSort] elementSort

    let private generateStoreOp newSortName newSort indexSort elementSort =
        let storeName = generateStoreName newSortName
        Operation.makeElementaryOperationFromSorts storeName [newSort; indexSort; elementSort] newSort

    let private addArraySortMapping ((arraySorts, originalSorts) as an) originalSort s1 s2 =
        match Map.tryFind originalSort arraySorts with
        | Some (newSort, _, _) -> newSort, an
        | None ->
            let newSortName = generateArraySortName s1 s2
            let newSort = PrimitiveSort newSortName
            let selectOp = generateSelectOp newSortName newSort s1 s2
            let storeOp = generateStoreOp newSortName newSort s1 s2
            let arraySorts = Map.add originalSort (newSort, selectOp, storeOp) arraySorts
            let originalSorts = Set.add originalSort originalSorts
            newSort, (arraySorts, originalSorts)

    let rec private mapSort arraySorts = function
        | PrimitiveSort _ as s -> s, arraySorts
        | ArraySort(s1, s2) as s ->
            let s1, arraySorts = mapSort arraySorts s1
            let s2, arraySorts = mapSort arraySorts s2
            addArraySortMapping arraySorts s s1 s2

    let private selectRelativization rels selectOp =
        let originalSelectOp = selectOp |> Operation.changeName "select"
        addShouldNotRelativize originalSelectOp selectOp rels

    let private storeRelativization rels storeOp =
        let originalStoreOp = storeOp |> Operation.changeName "store"
        addShouldNotRelativize originalStoreOp storeOp rels

    let private mapArraySorts (rels, arraySorts, eqs, diseqs) command =
        let command, (arraySorts, originalSorts) = MapSorts(mapSort).FoldCommand (arraySorts, Set.empty) command
        let arraySortsDeclarations, selectOps, storeOps = originalSorts |> Set.toList |> List.map (fun newSort -> Map.find newSort arraySorts) |> List.unzip3
        let arraySortsDeclarations = List.map DeclareSort arraySortsDeclarations
        let selectOpDeclarations = List.map declareOp selectOps
        let storeOpDeclarations = List.map declareOp storeOps
        let selectRels = List.fold selectRelativization Map.empty selectOps
        let storeRels = List.fold storeRelativization Map.empty storeOps
        let congrDeclarations, eqs, diseqs = Arrays.generateEqsAndDiseqs eqs diseqs originalSorts arraySorts
        let rels = Map.union selectRels (Map.union storeRels rels)
        let relativizer = SubstituteOperations(rels, eqs, diseqs)
        let command = relativizer.SubstituteOperationsWithRelations(command)
        List.map OriginalCommand (arraySortsDeclarations @ storeOpDeclarations @ selectOpDeclarations) @ congrDeclarations @ [command], (rels, arraySorts, eqs, diseqs)

    let substituteArraySorts (eqs, diseqs) commands =
        List.mapFold mapArraySorts (Map.empty, Map.empty, eqs, diseqs) commands |> fst |> List.concat

module private SubstIntWithNat =
    let private mapSort natSort () s =
        let rec mapSort = function
            | ArraySort(t1, t2) -> ArraySort(mapSort t1, mapSort t2)
            | s when s = integerSort -> natSort
            | s -> s
        mapSort s, ()

    let private substInCommand (mapper : MapSorts<unit>) natOps (natConstMap : ident -> term -> term) command =
        let command = mapper.MapCommand(command)
        let relativizer = SubstituteOperations(natOps, natConstMap)
        let command = relativizer.SubstituteOperationsWithRelations command
        command

    let substituteIntWithNat commands =
        let preambula, natSort, natOps, natConstMap = IntToNat.generateNatDeclarations ()
        let mapper = MapSorts(mapSort natSort)
        let natOps = natOps |> Map.toList |> List.map (fun (oldOp, newOp) -> mapper.MapOperation(oldOp), newOp) |> Map.ofList
        preambula @ List.map (substInCommand mapper natOps natConstMap) commands, natSort

module private SubstituteFreeSortsWithNat =

    let transformation freeSorts natSort (eqs, diseqs) commands =
        let mapSort () s = (if Set.contains s freeSorts then natSort else s), ()
        let mapper = MapSorts(mapSort).MapCommand
        let substFreeSortsInCommand = function
            | OriginalCommand(DeclareSort s) when Set.contains s freeSorts -> None
            | c -> Some (mapper c)
        let commands = List.choose substFreeSortsInCommand commands
        let commands = List.map (SubstituteOperations(Map.empty, eqs, diseqs).SubstituteOperationsWithRelations) commands
        commands

let toClauses needToApplyTIPfix commands =
    IdentGenerator.setup ()
    let commands = if needToApplyTIPfix then TIPFixes.applyTIPfix commands else commands
    let commandsWithUniqueVariableNames = RemoveVariableOverlapping.removeVariableOverlapping commands
    let freeSorts = commandsWithUniqueVariableNames |> List.choose (function Command(DeclareSort(s)) -> Some s | _ -> None) |> Set.ofList
    let hornClauses = DefinitionsToDeclarations.definesToDeclarations needToApplyTIPfix commandsWithUniqueVariableNames
    let relHornClauses = if needToApplyTIPfix then RelativizeSymbols.relativizeSymbols hornClauses else hornClauses
    let commandsWithoutInts, natSort = SubstIntWithNat.substituteIntWithNat relHornClauses
    let pureHornClauses, adtEqs = ADTs.SupplementaryADTAxioms.addSupplementaryAxioms commandsWithoutInts
    let arrayTransformedClauses = ArrayTransformations.substituteArraySorts adtEqs pureHornClauses
    let substFreeSortClauses = SubstituteFreeSortsWithNat.transformation freeSorts natSort adtEqs arrayTransformedClauses
    substFreeSortClauses
