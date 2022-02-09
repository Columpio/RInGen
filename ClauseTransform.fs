module RInGen.ClauseTransform
open RInGen
open RInGen.IntToNat
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

    let private cleanContextedExpr (typer, nameMap, sortMap) vars body =
        let vars, (nameMap, sortMap) = addSortedVars nameMap sortMap vars
        let te = VarEnv.create typer vars
        vars, cleanExpr (te, nameMap, sortMap) body

    let private cleanFuncDef typer (name, vars, sort, body) =
        let vars, body = cleanContextedExpr typer vars body
        name, vars, sort, body

    let private cleanLemma ((_, nameMap, _) as typer) pred vars body =
        let vars, body = cleanContextedExpr typer vars body
        Map.find pred nameMap, vars, body

    let private cleanCommand ((typr, nameMap, sortMap) as typer) = function
        | Command _ as c -> c
        | Definition(DefineFun df) -> cleanFuncDef typer df |> DefineFun |> Definition
        | Definition(DefineFunRec df) -> cleanFuncDef typer df |> DefineFunRec |> Definition
        | Definition(DefineFunsRec dfs) -> dfs |> List.map (cleanFuncDef typer) |> DefineFunsRec |> Definition
        | Assert f -> f |> cleanExpr ((typr, VarEnv.empty), nameMap, sortMap) |> Assert
        | Lemma(pred, vars, e) -> cleanLemma typer pred vars e |> Lemma

    let private substWithNameMap nameMap s = Map.find s nameMap
    let rec private substWithSortMap sortMap s =
        match Map.tryFind s sortMap with
        | Some s -> s
        | None ->
            match s with
            | PrimitiveSort _ -> s
            | CompoundSort(name, sorts) -> CompoundSort(name, List.map (substWithSortMap sortMap) sorts)
    let private substWithNameMapList nameMap = List.map (substWithNameMap nameMap)
    let private substWithSortMapList sortMap = List.map (substWithSortMap sortMap)
    let private substWithNameMapPairList nameMap sortMap =  (fun (a, b) -> substWithNameMap nameMap a, substWithSortMap sortMap b)
    let private prepareDefinition (nameMap, sortMap) (name, args, retSort, body) =
        let newName = IdentGenerator.gensymp name
        let nameMap = Map.add name newName nameMap
        let args = List.map (fun (v, s) -> (v, substWithSortMap sortMap s)) args
        (newName, args, substWithSortMap sortMap retSort, body), (nameMap, sortMap)

    let private addDatatypeSorts (nameMap, sortMap) (name, cs) =
        let newName = Sort.gensym name
        (nameMap, Map.add name newName sortMap)
    let private substDatatypeSorts (nameMap, sortMap) (name, cs) =
        let mapTester nameMap constr newConstr =
            let tester = testerNameOf constr
            let newTester = testerNameOf newConstr
            Map.add tester newTester nameMap
        let mapSelector (nameMap, sortMap) (sel, sort) =
            let newSel = IdentGenerator.gensymp sel
            (newSel, substWithSortMap sortMap sort), (Map.add sel newSel nameMap, sortMap)
        let mapConstr (nameMap, sortMap) (constr, selectors) =
            let newConstr = IdentGenerator.gensymp constr
            let nameMap = Map.add constr newConstr nameMap
            let selectors, (nameMap, sortMap) = List.mapFold mapSelector (nameMap, sortMap) selectors
            let nameMap = mapTester nameMap constr newConstr
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
            let newName = Sort.gensym name
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

    let private renameIdentsInCommand (typer : Typer.Typer) (nameMap, sortMap) c =
        let nameMap, sortMap, c = prepareCommand nameMap sortMap c
        typer.m_interpretOriginalCommand c
        cleanCommand (typer, nameMap, sortMap) c, (nameMap, sortMap)

    let removeVariableOverlapping =
        let typer = Typer.empty ()
        List.mapFold (renameIdentsInCommand typer) (Map.empty, Map.empty) >> fst

module private DefinitionsToDeclarations =
    let assumeTrue x = [x], truet
    let assumeFalse x = [x], falset

    [<AutoOpen>]
    module private Choosable =
        type choosable<'a> = 'a conditional list
        let toChoosable x : 'a choosable = [Conditional.toCondition x]
        let combinations (oneToMany : 'a -> 'b choosable) : 'a list -> 'b list choosable = List.map oneToMany >> List.product >> List.map Conditional.list
        let map (f : 'a -> 'b) (ch : 'a choosable) : 'b choosable = List.map (Conditional.mapHead f) ch
        let strengthen conds (c : 'a choosable) : 'a choosable = List.map (Conditional.strengthen conds) c
        let flatten (xss : 'a choosable choosable) : 'a choosable =
            List.collect (fun (conds, xs) -> strengthen conds xs) xss
        let bind (f : 'a -> 'b choosable) (ch : 'a choosable) : 'b choosable = flatten <| map f ch
        let map2 f (x : 'a choosable) (y : 'b choosable) : 'c choosable = List.product2 x y |> List.map ((<||) (Conditional.map2 f))
        let destruct : term -> term choosable = function
            | TApply(ElementaryOperation("=", _, _), [t1; t2]) ->
                [assumeTrue <| Equal(t1, t2); assumeFalse <| Distinct(t1, t2)]
            | TApply(ElementaryOperation("distinct", _, _), [t1; t2]) ->
                [assumeFalse <| Equal(t1, t2); assumeTrue <| Distinct(t1, t2)]
            | TApply(NotT negop as op, ts) ->
                [assumeTrue <| AApply(op, ts); assumeFalse <| AApply(negop, ts)]
            | TConst _
            | TIdent _
            | TApply _ as t -> toChoosable t
        let toDNF : atom choosable -> dnf = Disjunction << List.map Conditional.toConj

    let private binaryApplyToOp zero one op xs =
        if List.contains one xs then one else
        let binaryApplyToOp x y = TApply(op, [x; y])
        let xs = List.filter ((<>) zero) xs
        if xs = [] then zero else
        List.reduce binaryApplyToOp xs
    let private mapBoolOperator f ts =
        let trueAndFalseCombinations ts : term choosable =
            let ts = Choosable.combinations Choosable.destruct ts
            Choosable.map f ts
        Choosable.bind trueAndFalseCombinations ts
    let private bindBoolOperator f ts =
        let trueAndFalseCombinations ts : term choosable =
            let ts = Choosable.combinations Choosable.destruct ts
            Choosable.bind f ts
        Choosable.bind trueAndFalseCombinations ts
    let private tand = mapBoolOperator (binaryApplyToOp truet falset DummyOperations.andOp)
    let private tor = mapBoolOperator (binaryApplyToOp falset truet DummyOperations.orOp)
//    let private ahence ts = TApply(DummyOperations.henceOp, ts)
    let private tnot t = TApply(DummyOperations.notOp, [t])
//    let private anot ts = Equal(tnot ts, truet)

    let private negateDNF typer e : dnf =               // expr   !((is-A x /\ is-B y) \/ (is-A z /\ is-B t))
        let dnf_e = e                                   //          (is-A x /\ is-B y) \/ (is-A z /\ is-B t)
        let cnf_e = DNF.flip dnf_e                      // ~flip~>  (is-A x \/ is-B y) /\ (is-A z \/ is-B t)
        let neg_cnf_e = Conj.bind (nota typer) cnf_e    // ~not~>   (is-B x \/ is-A y) /\ (is-B z \/ is-A t)
        let dnf_neg_e = Conj.exponent neg_cnf_e         // ~dnf~>   (is-B x /\ is-b z) \/ (is-B x /\ is-A t) \/ ...
        dnf_neg_e

    let rec private atomToTerm = function
//        | AApply(op, ts) -> TApply(op, ts)
//        | Distinct(t, t2) when t2 = truet -> TApply(DummyOperations.notOp, [t])
//        | ANot t -> TApply(DummyOperations.notOp, [atomToTerm t])
        | t -> failwithf $"Can't obtain term from atom: {t}"

    let rec private exprToTerm atomsAreTerms : smtExpr -> term choosable = function
        | Ident(name, sort) -> TIdent(name, sort) |> toChoosable
        | BoolConst b -> (if b then truet else falset) |> toChoosable
        | Number n -> TConst(toString n, integerSort) |> toChoosable //TODO: IntToNat
        | Apply(op, ts) ->
            let toChoose ts = TApply(op, ts) |> Choosable.destruct
            bindBoolOperator toChoose (exprsToTerms atomsAreTerms ts)
        | Not (Not e) -> exprToTerm atomsAreTerms e
        | Not e -> e |> exprToTerm atomsAreTerms |> List.map (fun (cs, t) -> cs, tnot t)
        | Or es -> tor <| exprsToTerms atomsAreTerms es
        | And es -> tand <| exprsToTerms atomsAreTerms es
//        | Hence(a, b) -> TApply(DummyOperations.henceOp, [exprToTerm atomsAreTerms a; exprToTerm atomsAreTerms b])
        | t -> failwithf $"Can't obtain term from expr: {t}"
    and private exprsToTerms atomsAreTerms = Choosable.combinations (exprToTerm atomsAreTerms)

    and private exprToAtoms (typer : Typer) atomsAreTerms e : dnf =
        match e with
        | Ident(name, s) when s = boolSort ->
            if typer.containsKey name
                then DNF.singleton <| AApply(identToUserOp name s, [])
                else DNF.singleton <| Equal(TIdent(name, s), truet)
        | Not (Not t) -> exprToAtoms typer atomsAreTerms t
        | Not e -> exprToAtoms typer atomsAreTerms e |> negateDNF typer
        | BoolConst true -> DNF.singleton <| Top
        | BoolConst false -> DNF.singleton <| Bot
        | Apply(UserDefinedOperation(_, _, s) as op, ts) when s = boolSort ->
            let toAtom = if atomsAreTerms then fun ts -> Equal(TApply(op, ts), truet) else fun ts -> AApply(op, ts)
            exprsToTerms atomsAreTerms ts
            |> Choosable.map toAtom
            |> Choosable.toDNF
        | Or ts -> Disj.disj <| List.map (exprToAtoms typer atomsAreTerms) ts
//        | Hence(a, b) -> [AHence(aand <| exprToAtoms atomsAreTerms a, aand <| exprToAtoms atomsAreTerms b)]
        | And ts -> exprsToAtoms typer atomsAreTerms ts
        | Apply(ElementaryOperation("=", _, _), [t1; t2]) ->
            Choosable.map2 (fun t1 t2 -> Equal(t1, t2)) (exprToTerm atomsAreTerms t1) (exprToTerm atomsAreTerms t2) |> Choosable.toDNF
        | Apply(ElementaryOperation("distinct", _, _), [t1; t2]) ->
            Choosable.map2 (fun t1 t2 -> Distinct(t1, t2)) (exprToTerm atomsAreTerms t1) (exprToTerm atomsAreTerms t2) |> Choosable.toDNF
        | Apply(ElementaryOperation(_, _, s) as op, ts) when s = boolSort ->
            exprsToTerms atomsAreTerms ts
            |> Choosable.map (fun ts -> AApply(op, ts))
            |> Choosable.toDNF
        | t -> failwithf $"Can't obtain atom from expr: {t}"
    and private exprsToAtoms typer atomsAreTerms = List.map (exprToAtoms typer atomsAreTerms) >> Disj.conj

    let private functionExprToTerm = exprToTerm true

    let rec private toRuleProduct tes args =
        let combine2 arg st =
            let arg = exprToRule tes arg
            collector {
                let! v, a, r = st
                let! v', a', r' = arg
                return Quantifiers.combine v' v, a' @ a, r' :: r
            }
        List.foldBack combine2 args [Quantifiers.empty, [], []]
    and private toRuleHandleProduct tes constructor ts =
        collector {
            let! vs, cs, rs = toRuleProduct tes ts
            return vs, cs, constructor rs
        }
    and private exprToRule ((typer : Typer, _ as te), subst as tes) = function
        | Apply(op, ts) -> toRuleHandleProduct tes (fun ts -> Apply(op, ts)) ts
        | Ident(name, sort) when sort = boolSort && Map.containsKey name subst -> Map.find name subst
        | Ident _
        | Number _
        | BoolConst _ as e -> [Quantifiers.empty, [], e]
        | And fs -> toRuleHandleProduct tes ande fs
        | Or fs -> toRuleHandleProduct tes ore fs
        | Hence(a, b) ->
            collector {
                let! avs, acs, ar = exprToRule tes a
                let! bvs, bcs, br = exprToRule tes b
                return Quantifiers.combine (Quantifiers.negate avs) bvs, acs @ bcs, Hence(ar, br)
            }
        | Not e ->
            collector {
                let! vs, cs, r = exprToRule tes e
                return Quantifiers.negate vs, cs, note r
            }
        | Forall(vars, body) ->
            let tes = VarEnv.replace te vars, subst
            collector {
                let! bodyVars, bodyConditions, bodyResult = exprToRule tes body
                return Quantifiers.combine (Quantifiers.forall vars) bodyVars, bodyConditions, bodyResult
            }
        | Exists(vars, body) ->
            let tes = VarEnv.replace te vars, subst
            collector {
                let! bodyVars, bodyConditions, bodyResult = exprToRule tes body
                return Quantifiers.combine (Quantifiers.exists vars) bodyVars, bodyConditions, bodyResult
            }
        | Let(assignments, body) ->
            let handleAssignment (te, subst) (v, expr) =
                let tes = VarEnv.replaceOne te v, subst
                match v with
                | (name, b) when b = boolSort ->
                    let e = exprToRule tes expr
                    [Quantifiers.empty, []], (te, Map.add name e subst)
                | _ ->
                    collector {
                        let! exprvs, exprcs, expr = exprToRule tes expr
                        let! exprConds, expr = functionExprToTerm expr
                        return Quantifiers.combine (Quantifiers.stableforall [v]) exprvs, (Equal(TIdent v, expr) :: exprConds @ exprcs)
                    }, (te, subst)
            let assignments, tes = List.mapFold handleAssignment tes assignments  // [[even; odd]; [0mod3; 1mod3; 2mod3]]
            collector {
                let! assignments = List.product assignments                     // [[even; 0mod3]; [even; 1mod3]; ...]
                let vars, conds = List.unzip assignments
                let vars = List.reduceBack Quantifiers.combine vars
                let conds = List.concat conds
                let! bodyvs, bodycs, body = exprToRule tes body
                return Quantifiers.combine vars bodyvs, conds @ bodycs, body
            }
        | Match(expr, cases) ->
            let handle_case patterns (pattern, body) =
                let varsList = ADTExtensions.getFreeVarsFromPattern typer pattern
                let tes = VarEnv.replace te varsList, subst
                let body =
                    exprToRule tes body
                    |> List.map (fun (vars', assumptions, body) -> pattern, patterns, Quantifiers.combine (Quantifiers.stableforall varsList) vars', assumptions, body)
                body, pattern::patterns
            let expr = exprToRule tes expr
            let cases = List.mapFold handle_case [] cases |> fst |> List.concat
            collector {
                let! tvars, tassumptions, tretExpr = expr
                let! tretExprConds, tretExpr = functionExprToTerm tretExpr
                let! pattern, patterns, brvars, brassumptions, brretExpr = cases
                let! pvars, patConds, pattern_match = ADTExtensions.patternsToConstraints typer patterns pattern tretExpr functionExprToTerm
                return Quantifiers.combine (Quantifiers.stableforall pvars) (Quantifiers.combine tvars brvars), pattern_match :: tretExprConds @ patConds @ tassumptions @ brassumptions, brretExpr
            }
        | Ite(i, t, e) ->
            collector {
                let! ivs, ics, ir = exprToRule tes i
                let! tvs, tcs, tr = exprToRule tes t
                let! evs, ecs, er = exprToRule tes e
                let thenBranchQuantifiers = Quantifiers.combine ivs tvs
                let elseBranchQuantifiers = Quantifiers.combine ivs evs
                let! Conjunction thenBranchConditions = exprToAtoms typer true ir |> Disj.get
                let! Conjunction elseBranchConditions = exprToAtoms typer true (note ir) |> Disj.get
                let thenBranch = thenBranchQuantifiers, thenBranchConditions @ ics @ tcs, tr
                let elseBranch = elseBranchQuantifiers, elseBranchConditions @ ics @ ecs, er
                return! [thenBranch; elseBranch]
            }

    let private definitionToDeclaration (name, vars, sort, _) =
        let argTypes = List.map snd vars
        let decl = DeclareFun(name, argTypes, sort)
        name, OriginalCommand decl

    let private defineOperationName = symbol "*define*"
    let private defineOperation call body = Operation.makeElementaryOperationFromSorts defineOperationName [Term.typeOf call; Term.typeOf body] boolSort
    let (|DefineOperation|_|) = function
        | AApply(ElementaryOperation(name, [_; _], s), [call; bodyResult]) when name = defineOperationName && s = boolSort -> Some (call, bodyResult)
        | _ -> None
    let private connectFunctionCallWithBody call bodyResult =
        collector {
            let! conds, bodyResult = functionExprToTerm bodyResult
            return conds, AApply(defineOperation call bodyResult, [call; bodyResult])
        }
    let private connectFunctionNameWithBody userFuncOp args bodyResult = connectFunctionCallWithBody (TApply(userFuncOp, List.map TIdent args)) bodyResult

    let private finalRule vars qbvars qhvars conds result =
        let qs = Quantifiers.combine (Quantifiers.forall vars) (Quantifiers.combine (Quantifiers.negate qbvars) qhvars)
        Rule(qs, conds, result)

    let private definitionToAssertion typer (name, vars, sort, body) =
        let userFuncOp = Operation.makeUserOperationFromVars name vars sort
        collector {
            let! bodyVars, bodyConditions, bodyResult = exprToRule (VarEnv.create typer vars, Map.empty) body
            let! conds, bodyResult = connectFunctionNameWithBody userFuncOp vars bodyResult
            let body = finalRule vars Quantifiers.empty bodyVars (conds @ bodyConditions) bodyResult
            return TransformedCommand body
        }

    let private expressionToDeclarations assertsToQueries typer =
        let rec eatCondition = function
            | And cs -> List.collect eatCondition cs
            | c -> [c]
        let isPredicate = function AApply(UserDefinedOperation _, _) -> true | _ -> false
//        let resultTerm t =
//            let (Disjunction conjs) = exprToAtoms typer assertsToQueries t
//            let predicates, constraints = List.partition hasPredicate conjs
//            let constraint_in_body = negateDNF typer <| Disjunction constraints
//            match predicates with
//            | [] -> constraint_in_body, Bot
//            | [Conjunction [pred]] -> constraint_in_body, pred
//            | ts -> failwithf $"Too many atoms in head: {ts}"
        let resultTerm =
            notMapApply (fun op ts -> [], AApply(op, ts)) (fun r -> [r], Bot)
        let takeHead = function
            | Disjunction [Conjunction [pred]] -> [resultTerm pred]
            | ts ->
                match Disj.exponent ts with
                | Conjunction [Disjunction ts] ->
                    // P \/ Q -> T = !(P \/ Q) \/ T = (!P /\ !Q) \/ T = !P \/ T, !Q \/ T = P -> T, Q -> T
                    // is-A x \/ is-B y
                    // !(is-A x) /\ !(is-B y) -> _|_
                    // (is-B x \/ is-C x) /\ (is-A y \/ is-C y) -> _|_
                    // is-B x /\ is-A y \/ is-B x /\ is-C y \/ is-C x /\ is-A y \/ is-C x /\ is-C y -> _|_
                    let predicates, constraints = List.partition isPredicate ts
                    let (Disjunction constraints) = Conj.map (nota typer) (Conjunction constraints) |> Conj.exponent
                    match predicates with
                    | [] -> List.map (function Conjunction constraints -> constraints, Bot) constraints
                    | [pred] -> List.map (function Conjunction constraints -> constraints, pred) constraints
                    | ts -> failwithf $"Too many atoms in head: {ts}"
                | ts -> failwithf $"Too many atoms in head: {ts}"
        let rec eatResultTerm conds = function
            | Hence(cond, body) -> eatResultTerm (eatCondition cond @ conds) body
            | Not cond -> eatResultTerm (eatCondition cond @ conds) falsee
            | And _ as ts -> //TODO: something is completely wrong here. test result has (assert false) things...
                let ts = eatCondition ts
                List.map (fun t -> conds, t) ts
            | t -> [conds, t]
        let rec eat vars conds = function
            | Forall(vars', body) -> eat (vars @ vars') conds body
            | Or es ->
                let apps, rest = List.partition (function Apply(UserDefinedOperation(_, _, s), _) when s = boolSort -> true | _ -> false) es
                let body = List.map note rest
                match apps with
                | [] -> eat vars conds (hence body falsee)
                | [app] -> eat vars conds (hence body app)
                | _ -> failwithf $"Disjunction in clause head: %O{apps}"
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
                let tes = VarEnv.create typer vars, Map.empty
                collector {
                    let! appVars, appConditions, appResult = exprToRule tes app
                    let! bodyAddition = if assertsToQueries then exprToAtoms typer assertsToQueries (note appResult) else DNF.empty
                    let! headConds, head = if assertsToQueries then [[], falsee] else eatResultTerm [] appResult
                    let! bodyVars, bodyConditions, bodyResult = toRuleProduct tes (conds @ headConds)
                    let! bodyResult = List.map (exprToAtoms typer assertsToQueries) bodyResult |> Disj.conj
                    let! headConstraints, head_atom = exprToAtoms typer assertsToQueries head |> takeHead
                    let r = finalRule vars bodyVars appVars (headConstraints @ bodyAddition @ bodyResult @ bodyConditions @ appConditions) head_atom // TODO: not Bot
                    return TransformedCommand r
                }
        eat [] []

    let private dropWeakLiterals (typer : Typer) vars lemmaQs lemmaConds lemmaFOL =
        let dropWeak = function
            | Equal(t1, t2)
            | Distinct(t1, t2) as a when not (ADTExtensions.isGround t1 || ADTExtensions.isGround t2) -> a |> FOLAtom |> Some
            | _ -> None
        let dropWeak = function
            | FOLAtom a -> dropWeak a
            | f -> Some f
        match Simplification.simplifyConditional typer.isConstructor (Set.ofList vars) lemmaQs lemmaConds (fun unifier -> FOL.substituteWith unifier lemmaFOL) with
        | None -> []
        | Some (lemmaQs, lemmaConds, lemmaFOL) ->
        let strongLemma =
            match lemmaFOL with
            | FOLOr fs -> fs |> List.choose dropWeak |> folOr
            | FOLAtom _ as a -> dropWeak a |> Option.defaultValue (FOLAtom Bot)
            | f -> f
        [lemmaQs, (lemmaConds, strongLemma)]

    let private doubleNegateLemma typer = FOL.bind (nota typer >> List.map (FOLAtom >> folNot) >> folAnd)

    let private replaceDisequalWithDistinctInLemma (qs, (conds, lemma)) =
        let diseq = Map.find "distinct" Operations.elementaryOperations |> Operation.flipOperationKind
        let replaceAtom = function
            | Distinct(t1, t2) -> AApply(diseq, [t1; t2])
            | a -> a
        let conds = List.map replaceAtom conds
        let lemma = FOL.map replaceAtom lemma
        qs, (conds, lemma)

    let rec private defineCommandToDeclarations assertsToQueries typer wereDefines = function
        | Definition(DefineFun df)
        | Definition(DefineFunRec df) ->
            let name, def = definitionToDeclaration df
            def :: definitionToAssertion typer df, Set.add name wereDefines
        | Definition(DefineFunsRec dfs) ->
            let names, defs = List.map definitionToDeclaration dfs |> List.unzip
            defs @ List.collect (definitionToAssertion typer) dfs, Set.union (Set.ofList names) wereDefines
        | Lemma(pred, vars, lemma) ->
            let tes = VarEnv.create typer vars, Map.empty
            collector {
                let! lemmaQs, lemmaConds, lemmaBody = exprToRule tes lemma
                let lemma = exprToAtoms typer assertsToQueries lemmaBody
                let lemmaFOL = lemma |> DNF.toFOL
                let! lemmaQs, (lemmaConds, strongLemma) = dropWeakLiterals typer vars lemmaQs lemmaConds lemmaFOL
                let bodyLemma : lemma = lemmaQs, (lemmaConds, strongLemma)
                let doubleNegatedLemma = doubleNegateLemma typer strongLemma
                let headCube = Lemma.withFreshVariables(lemmaQs, (lemmaConds, doubleNegatedLemma))
                return LemmaCommand(pred, vars, bodyLemma, headCube)
            }, wereDefines
        | Assert e -> expressionToDeclarations assertsToQueries typer e, wereDefines
        | Command c -> [OriginalCommand c], wereDefines

    let definesToDeclarations assertsToQueries commands =
        let commands, wereDefines = Typer.typerMapFold (defineCommandToDeclarations assertsToQueries) Set.empty commands
        List.concat commands, wereDefines

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
        | Lemma _
        | Command _ as c -> c
        | Definition df -> df |> invertMatchesInDefinition |> Definition

    let applyTIPfix commands =
        let commands = List.map (function Assert(Not(Forall(vars, body))) -> Assert(Forall(vars, body)) | c -> c) commands
        List.map invertMatches commands

module private RelativizeSymbols =
    open DefinitionsToDeclarations
    let private addNewSymbolsToRelativize wereDefines rels = function
        | OriginalCommand(DeclareFun(name, args, ret)) when Set.contains name wereDefines ->
            let op = Operation.makeUserOperationFromSorts name args ret
            addShouldRelativize op (Relativization.relativizeOperation op) rels
        | _ -> rels

    let private assertIsFunction name args ret =
        let op = Operation.makeUserOperationFromSorts name args ret |> relativizeOperation
        let args = args |> List.map (fun s -> IdentGenerator.gensym (), s)
        let ret = IdentGenerator.gensym (), ret
        aerule args [ret] [] (relapply op (List.map TIdent args) (TIdent ret))

    let private splitHasResult cs call =
        let rec iter cs k =
            match cs with
            | AApply(_, t::_) as c ::cs when t = call -> c, k cs
            | c::cs -> iter cs (fun cs -> k <| c :: cs)
            | [] -> __unreachable__()
        iter cs id

    let private relativizeDeclarations wereDefines = function
        | OriginalCommand(DeclareFun(name, args, ret)) when Set.contains name wereDefines ->
            let decl = reldeclare name args ret
//            let assertNonEmpty = TransformedCommand <| assertIsFunction name args ret
            [OriginalCommand decl]
        | TransformedCommand(Rule(vars, cs, DefineOperation(call, bodyResult))) ->
            let c, cs = splitHasResult cs call
            [Rule(vars, Equal(call, bodyResult)::cs, c) |> TransformedCommand]
        | c -> [c]

    let relativizeSingleCommand wereDefines rels command =
        let rels = addNewSymbolsToRelativize wereDefines rels command
        let relativizer = SubstituteOperations(rels)
        let command = relativizer.SubstituteOperationsWithRelations(command)
        command, rels

    let relativizeSymbols wereDefines commands =
        let commands, _ = List.mapFold (relativizeSingleCommand wereDefines) Map.empty commands
        List.collect (relativizeDeclarations wereDefines) commands

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

module private ArrayTransformations =

    let private generateArraySortName s1 s2 = IdentGenerator.gensymp ("Array" + Sort.sortToFlatString s1 + Sort.sortToFlatString s2)
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
        | CompoundSort(name, sorts) ->
            let sorts, arraySorts = List.mapFold mapSort arraySorts sorts
            CompoundSort(name, sorts), arraySorts

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
        let selectOpDeclarations = List.map Operation.declareOp selectOps
        let storeOpDeclarations = List.map Operation.declareOp storeOps
        let selectRels = List.fold selectRelativization Map.empty selectOps
        let storeRels = List.fold storeRelativization Map.empty storeOps
        let congrDeclarations, eqs, diseqs = Arrays.generateEqsAndDiseqs eqs diseqs originalSorts arraySorts
        let rels = Map.union selectRels (Map.union storeRels rels)
        let relativizer = SubstituteOperations(rels, eqs, diseqs)
        let command = relativizer.SubstituteOperationsWithRelations(command)
        List.map OriginalCommand (arraySortsDeclarations @ storeOpDeclarations @ selectOpDeclarations) @ congrDeclarations @ [command], (rels, arraySorts, eqs, diseqs)

    let substituteArraySorts (eqs, diseqs) commands =
        List.mapFold mapArraySorts (Map.empty, Map.empty, eqs, diseqs) commands |> fst |> List.concat

module private SubstituteFreeSortsWithNat =

    let transformation freeSorts natSort (eqs, diseqs) commands =
        let mutable wasSubstituted = false
        let mapSort () s = (if Set.contains s freeSorts then wasSubstituted <- true; natSort else s), ()
        let mapper = MapSorts(mapSort).MapCommand
        let substFreeSortsInCommand = function
            | OriginalCommand(DeclareSort s) when Set.contains s freeSorts -> None
            | c -> Some (mapper c)
        let commands = List.choose substFreeSortsInCommand commands
        let commands = List.map (SubstituteOperations(Map.empty, eqs, diseqs).SubstituteOperationsWithRelations) commands
        wasSubstituted, commands

let private filterOutSMTCommands commands =
    let filterOutSMTCommand = function
        | DeclareConst _
        | DeclareFun _
        | DeclareSort _
        | DeclareDatatype _
        | DeclareDatatypes _ -> true
        | _ -> false
    List.filter (function Command c -> filterOutSMTCommand c | _ -> true) commands

module SubstituteLemmas =
    let private freshLemmaPredicate pred vars =
        Operation.makeUserRelationFromVars (IdentGenerator.gensymp("Lemma_"+pred)) vars

    let private callLemmaOn lemmaOp vars lemma conds qs ts =
        let varsToTerms = Map.ofList <| List.zip vars ts
        let qs, freshVarsMap = Quantifiers.withFreshVariables qs
        let varsMap = Map.map (fun _ -> TIdent) freshVarsMap |> Map.union varsToTerms
        let lemma = folOr [FOL.substituteWith varsMap lemma; FOLAtom <| AApply(lemmaOp, ts)]
        let conds = List.map (Atom.substituteWith varsMap) conds
        lemma, conds, qs

    let private substitutePredicateCallWithLemmas pos lemmas ts =
        let substitutePredicateCallWithLemma (lemmaOp, vars, bl, hl) =
            let qs, (conds, lemma) = if pos then hl else bl
            callLemmaOn lemmaOp vars lemma conds qs ts
        let lemmaPieces, conds, qs = lemmas |> List.map substitutePredicateCallWithLemma |> List.unzip3
        let q = Quantifiers.combineMany qs
        folAnd lemmaPieces, List.concat conds, q

    let private mapAtom pos lemmasMap = function
        | AApply(op, ts) as a ->
            match Map.tryFind (Operation.opName op) lemmasMap with
            | Some lemmas -> substitutePredicateCallWithLemmas pos lemmas ts
            | None -> FOLAtom a, [], Quantifiers.empty
        | a -> FOLAtom a, [], Quantifiers.empty

    let private mapRule lemmasMap qs body head =
        let head, headConds, headQ = mapAtom true lemmasMap head
        let body, bodyConds, bodyQs = List.map (mapAtom false lemmasMap) body |> List.unzip3
        let body = List.map folNot (headConds::bodyConds |> List.concat |> List.map FOLAtom |> List.append body)
        let f = folOr (head::body)
        let q = Quantifiers.combineMany (qs :: headQ :: bodyQs)
        q, f

    let private mapCommand lemmasMap = function
        | OriginalCommand(DeclareFun(pred, _, _) as c) ->
            match Map.tryFind pred lemmasMap with
            | None -> [c]
            | Some lemmas -> lemmas |> List.map (fun (op, _, _, _) -> Operation.declareOp op)
            |> List.map FOLOriginalCommand
        | OriginalCommand c -> [FOLOriginalCommand c]
        | TransformedCommand(Rule(qs, body, head)) -> mapRule lemmasMap qs body head |> folAssert |> Option.toList
        | LemmaCommand _ -> []

    let private collectAllLemmas commands =
        let addLemma lemmasMap (pred, vars, bl, hl) =
            match Map.tryFind pred lemmasMap with
            | Some vbhs -> Map.add pred ((vars, bl, hl) :: vbhs) lemmasMap
            | None -> Map.add pred [(vars, bl, hl)] lemmasMap
        let lemmas, commands = List.choose2 (function LemmaCommand(pred, vars, bl, hl) -> Choice1Of2(pred, vars, bl, hl) | c -> Choice2Of2 c) commands
        let lemmasMap = List.fold addLemma Map.empty lemmas
        lemmasMap, commands

    let substituteLemmas commands =
        let lemmasMap, commands = collectAllLemmas commands
        let lemmasMap = Map.map (fun pred -> List.map (fun (vars, bl, hl) -> freshLemmaPredicate pred vars, vars, bl, hl)) lemmasMap
        List.collect (mapCommand lemmasMap) commands

module private Simplify =
    let private simplifyCommand (typer : Typer) = function
        | TransformedCommand(Rule(qs, body, head)) ->
            match Simplification.simplifyConditional typer.isConstructor Set.empty qs body (fun unifier -> Atom.substituteWith unifier head) with
            | None -> None
            | Some (qs, body, head) -> Some (TransformedCommand(Rule(qs, body, head)))
        | c -> Some c

    let simplify commands = Typer.typerMap simplifyCommand commands |> List.choose id

let toClauses (options : transformOptions) commands =
    let commands = filterOutSMTCommands commands
    let commands = if options.tip then TIPFixes.applyTIPfix commands else commands
    let commandsWithUniqueVariableNames = RemoveVariableOverlapping.removeVariableOverlapping commands
    let freeSorts = commandsWithUniqueVariableNames |> List.choose (function Command(DeclareSort(s)) -> Some s | _ -> None) |> Set.ofList
    let hornClauses, wereDefines = DefinitionsToDeclarations.definesToDeclarations options.tip commandsWithUniqueVariableNames
    let relHornClauses = RelativizeSymbols.relativizeSymbols wereDefines hornClauses
    let relHornClauses = BoolAxiomatization.BoolAxiomatization().SubstituteTheory relHornClauses
    let alreadyAddedNatPreamble, natPreamble, commandsWithoutInts, natSort = IntToNat().SubstituteTheoryDelayed relHornClauses
    let pureHornClauses, adtEqs = ADTs.SupplementaryADTAxioms.addSupplementaryAxioms commandsWithoutInts
    let natPreamble, adtEqs = if alreadyAddedNatPreamble then natPreamble, adtEqs else ADTs.SupplementaryADTAxioms.addSupplementaryAxiomsIncremental adtEqs natPreamble
    let arrayTransformedClauses = ArrayTransformations.substituteArraySorts adtEqs pureHornClauses
    let shouldAddNatPreamble, substFreeSortClauses = SubstituteFreeSortsWithNat.transformation freeSorts natSort adtEqs arrayTransformedClauses
    let clausesWithPreamble = if not alreadyAddedNatPreamble && shouldAddNatPreamble then natPreamble @ substFreeSortClauses else substFreeSortClauses
    let simplified = Simplify.simplify clausesWithPreamble
    let trCtx = {commands=simplified; diseqs=snd adtEqs}
    if options.sync_terms then
        let syncClauses = Synchronization.synchronize clausesWithPreamble
        {trCtx with commands = syncClauses}
    else if options.tta_transform then
        let ttaClauses = TtaTransform.transform clausesWithPreamble
        {trCtx with commands = ttaClauses}
    else
        trCtx