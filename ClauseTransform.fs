module RInGen.ClauseTransform
open RInGen
open RInGen.IntToNat
open RInGen.Context
open RInGen.SMTExpr
open Relativization
open SubstituteOperations
open Operations

module private DefinitionsToDeclarations =
    let assumeTrue x = [x], Term.truth
    let assumeFalse x = [x], Term.falsehood

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
    let private tand = mapBoolOperator (binaryApplyToOp Term.truth Term.falsehood DummyOperations.andOp)
    let private tor = mapBoolOperator (binaryApplyToOp Term.falsehood Term.truth DummyOperations.orOp)
//    let private ahence ts = TApply(DummyOperations.henceOp, ts)
    let private tnot t = TApply(DummyOperations.notOp, [t])
//    let private anot ts = Equal(tnot ts, Term.truth)

    let private negateDNF (ctx : Context) e : dnf =               // expr   !((is-A x /\ is-B y) \/ (is-A z /\ is-B t))
        let dnf_e = e                                   //          (is-A x /\ is-B y) \/ (is-A z /\ is-B t)
        let cnf_e = DNF.flip dnf_e                      // ~flip~>  (is-A x \/ is-B y) /\ (is-A z \/ is-B t)
        let neg_cnf_e = Conj.bind ctx.Not cnf_e    // ~not~>   (is-B x \/ is-A y) /\ (is-B z \/ is-A t)
        let dnf_neg_e = Conj.exponent neg_cnf_e         // ~dnf~>   (is-B x /\ is-b z) \/ (is-B x /\ is-A t) \/ ...
        dnf_neg_e

    let rec private atomToTerm = function
//        | AApply(op, ts) -> TApply(op, ts)
//        | Distinct(t, t2) when t2 = Term.truth -> TApply(DummyOperations.notOp, [t])
//        | ANot t -> TApply(DummyOperations.notOp, [atomToTerm t])
        | t -> failwithf $"Can't obtain term from atom: {t}"

    let rec private exprToTerm atomsAreTerms : smtExpr -> term choosable = function
        | Ident(name, sort) -> TIdent(name, sort) |> toChoosable
        | BoolConst b -> Term.fromBool b |> toChoosable
        | Number n -> TConst(toString n, IntSort) |> toChoosable //TODO: IntToNat
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

    and private exprToAtoms (ctx : Context) atomsAreTerms e : dnf =
        match e with
        | Ident(name, s) when s = BoolSort -> DNF.singleton <| Equal(TIdent(name, s), Term.truth)
        | Not (Not t) -> exprToAtoms ctx atomsAreTerms t
        | Not e -> exprToAtoms ctx atomsAreTerms e |> negateDNF ctx
        | BoolConst true -> DNF.singleton <| Top
        | BoolConst false -> DNF.singleton <| Bot
        | Apply(UserDefinedOperation(_, _, s) as op, ts) when s = BoolSort ->
            let toAtom = if atomsAreTerms then fun ts -> Equal(TApply(op, ts), Term.truth) else fun ts -> AApply(op, ts)
            exprsToTerms atomsAreTerms ts
            |> Choosable.map toAtom
            |> Choosable.toDNF
        | Or ts -> Disj.disj <| List.map (exprToAtoms ctx atomsAreTerms) ts
//        | Hence(a, b) -> [AHence(aand <| exprToAtoms atomsAreTerms a, aand <| exprToAtoms atomsAreTerms b)]
        | And ts -> exprsToAtoms ctx atomsAreTerms ts
        | Apply(ElementaryOperation("=", _, _), [t1; t2]) ->
            Choosable.map2 (fun t1 t2 -> Equal(t1, t2)) (exprToTerm atomsAreTerms t1) (exprToTerm atomsAreTerms t2) |> Choosable.toDNF
        | Apply(ElementaryOperation("distinct", _, _), [t1; t2]) ->
            Choosable.map2 (fun t1 t2 -> Distinct(t1, t2)) (exprToTerm atomsAreTerms t1) (exprToTerm atomsAreTerms t2) |> Choosable.toDNF
        | Apply(ElementaryOperation(_, _, s) as op, ts) when s = BoolSort ->
            exprsToTerms atomsAreTerms ts
            |> Choosable.map (fun ts -> AApply(op, ts))
            |> Choosable.toDNF
        | t -> failwithf $"Can't obtain atom from expr: {t}"
    and private exprsToAtoms ctx atomsAreTerms = List.map (exprToAtoms ctx atomsAreTerms) >> Disj.conj

    let private functionExprToTerm = exprToTerm true

    let private patternsToConstraints (ctx : Context) usedPatterns currentPattern exprToMatch toTerm =
        let tryGetHead = function Apply(op, _) -> Some op | _ -> None
        match currentPattern with
        | Ident(_, sort) -> // placeholder case
            let heads = List.choose tryGetHead usedPatterns
            let allConstructorNames = ctx.GetConstructors sort
            collector {
                let! op = Set.difference (Set.ofList allConstructorNames) (Set.ofList heads) |> Set.toList
                let args = Terms.generateVariablesFromOperation op
                return Terms.collectFreeVars args, [], Equal(exprToMatch, Term.apply op args)
            }
        | _ ->
            collector {
                let! conds, pat = toTerm currentPattern
                return [], conds, Equal(exprToMatch, pat)
            }
    
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
    and private exprToRule (env : SMTExpr.VarEnv, subst as tes) = function
        | Apply(op, ts) -> toRuleHandleProduct tes (fun ts -> Apply(op, ts)) ts
        | Ident(name, sort) when sort = BoolSort && Map.containsKey name subst -> Map.find name subst
        | Ident _
        | Number _
        | BoolConst _ as e -> [Quantifiers.empty, [], e]
        | And fs -> toRuleHandleProduct tes SMTExpr.ande fs
        | Or fs -> toRuleHandleProduct tes SMTExpr.ore fs
        | Hence(a, b) ->
            collector {
                let! avs, acs, ar = exprToRule tes a
                let! bvs, bcs, br = exprToRule tes b
                return Quantifiers.combine (Quantifiers.negate avs) bvs, acs @ bcs, Hence(ar, br)
            }
        | Not e ->
            collector {
                let! vs, cs, r = exprToRule tes e
                return Quantifiers.negate vs, cs, SMTExpr.note r
            }
        | QuantifierApplication(qs, body) ->
            env.InIsolation () {
                env.Add (Quantifiers.getVars qs)
                return collector {
                    let! bodyVars, bodyConditions, bodyResult = exprToRule tes body
                    return Quantifiers.combine qs bodyVars, bodyConditions, bodyResult
                }
            }
        | Let(assignments, body) ->
            let handleAssignment (te : VarEnv, subst) (v, expr) =
                v ||> te.AddOne
                match v with
                | name, BoolSort ->
                    let e = exprToRule tes expr
                    [Quantifiers.empty, []], (te, Map.add name e subst)
                | _ ->
                    collector {
                        let! exprvs, exprcs, expr = exprToRule tes expr
                        let! exprConds, expr = functionExprToTerm expr
                        return Quantifiers.combine (Quantifiers.stableforall [v]) exprvs, (Equal(TIdent v, expr) :: exprConds @ exprcs)
                    }, (te, subst)
            env.InIsolation () {
                let assignments, tes = List.mapFold handleAssignment tes assignments  // [[even; odd]; [0mod3; 1mod3; 2mod3]]
                return collector {
                    let! assignments = List.product assignments                     // [[even; 0mod3]; [even; 1mod3]; ...]
                    let vars, conds = List.unzip assignments
                    let vars = List.reduceBack Quantifiers.combine vars
                    let conds = List.concat conds
                    let! bodyvs, bodycs, body = exprToRule tes body
                    return Quantifiers.combine vars bodyvs, conds @ bodycs, body
                }
            }
        | Match(expr, cases) ->
            env.InIsolation () {
                let handle_case patterns (pattern, body) =
                    let varsList = ADTExtensions.getFreeVarsFromPattern pattern
                    env.Add varsList
                    let body =
                        exprToRule tes body
                        |> List.map (fun (vars', assumptions, body) -> pattern, patterns, Quantifiers.combine (Quantifiers.stableforall varsList) vars', assumptions, body)
                    body, pattern::patterns
                let expr = exprToRule tes expr
                let cases = List.mapFold handle_case [] cases |> fst |> List.concat
                return collector {
                    let! tvars, tassumptions, tretExpr = expr
                    let! tretExprConds, tretExpr = functionExprToTerm tretExpr
                    let! pattern, patterns, brvars, brassumptions, brretExpr = cases
                    let! pvars, patConds, pattern_match = patternsToConstraints env.ctx patterns pattern tretExpr functionExprToTerm
                    return Quantifiers.combine (Quantifiers.stableforall pvars) (Quantifiers.combine tvars brvars), pattern_match :: tretExprConds @ patConds @ tassumptions @ brassumptions, brretExpr
                }
            }
        | Ite(i, t, e) ->
            collector {
                let! ivs, ics, ir = exprToRule tes i
                let! tvs, tcs, tr = exprToRule tes t
                let! evs, ecs, er = exprToRule tes e
                let thenBranchQuantifiers = Quantifiers.combine ivs tvs
                let elseBranchQuantifiers = Quantifiers.combine ivs evs
                let! Conjunction thenBranchConditions = exprToAtoms env.ctx true ir |> Disj.get
                let! Conjunction elseBranchConditions = exprToAtoms env.ctx true (SMTExpr.note ir) |> Disj.get
                let thenBranch = thenBranchQuantifiers, thenBranchConditions @ ics @ tcs, tr
                let elseBranch = elseBranchQuantifiers, elseBranchConditions @ ics @ ecs, er
                return! [thenBranch; elseBranch]
            }

    let private definitionToDeclaration (name, vars, sort, _) =
        let argTypes = List.map snd vars
        let decl = DeclareFun(name, argTypes, sort)
        name, OriginalCommand decl

    let private defineOperationName = "*define*"
    let private defineOperation call body = Operation.makeElementaryOperationFromSorts defineOperationName [Term.typeOf call; Term.typeOf body] BoolSort
    let (|DefineOperation|_|) = function
        | AApply(ElementaryOperation(name, [_; _], s), [call; bodyResult]) when name = defineOperationName && s = BoolSort -> Some (call, bodyResult)
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

    let private definitionToAssertion ctx (name, vars, sort, body) =
        let userFuncOp = Operation.makeUserOperationFromVars name vars sort
        collector {
            let! bodyVars, bodyConditions, bodyResult = exprToRule (VarEnv(ctx).WithVars(vars), Map.empty) body
            let! conds, bodyResult = connectFunctionNameWithBody userFuncOp vars bodyResult
            let body = finalRule vars Quantifiers.empty bodyVars (conds @ bodyConditions) bodyResult
            return TransformedCommand body
        }

    let private expressionToDeclarations assertsToQueries (ctx : Context) =
        let rec eatCondition = function
            | And cs -> List.collect eatCondition cs
            | c -> [c]
        let isPredicate = function AApply(UserDefinedOperation _, _) -> true | _ -> false
//        let resultTerm t =
//            let (Disjunction conjs) = exprToAtoms ctx assertsToQueries t
//            let predicates, constraints = List.partition hasPredicate conjs
//            let constraint_in_body = negateDNF ctx <| Disjunction constraints
//            match predicates with
//            | [] -> constraint_in_body, Bot
//            | [Conjunction [pred]] -> constraint_in_body, pred
//            | ts -> failwithf $"Too many atoms in head: {ts}"
        let resultTerm =
            let withPremise = function
                | Top -> [[], Bot]
                | Bot -> []
                | r -> [[r], Bot]
            notMapApply (fun op ts -> [[], AApply(op, ts)]) withPremise
        let takeHead = function
            | Disjunction [Conjunction [pred]] -> resultTerm pred
            | ts ->
                match Disj.exponent ts with
                | Conjunction [Disjunction ts] ->
                    // P \/ Q -> T = !(P \/ Q) \/ T = (!P /\ !Q) \/ T = !P \/ T, !Q \/ T = P -> T, Q -> T
                    // is-A x \/ is-B y
                    // !(is-A x) /\ !(is-B y) -> _|_
                    // (is-B x \/ is-C x) /\ (is-A y \/ is-C y) -> _|_
                    // is-B x /\ is-A y \/ is-B x /\ is-C y \/ is-C x /\ is-A y \/ is-C x /\ is-C y -> _|_
                    let predicates, constraints = List.partition isPredicate ts
                    let (Disjunction constraints) = Conj.map ctx.Not (Conjunction constraints) |> Conj.exponent
                    match predicates with
                    | [] -> List.map (function Conjunction constraints -> constraints, Bot) constraints
                    | [pred] -> List.map (function Conjunction constraints -> constraints, pred) constraints
                    | ts -> failwithf $"Too many atoms in head: {ts}"
                | ts -> failwithf $"Too many atoms in head: {ts}"
        let rec eatResultTerm conds = function
            | Hence(cond, body) -> eatResultTerm (eatCondition cond @ conds) body
            | Not cond -> eatResultTerm (eatCondition cond @ conds) SMTExpr.falsehood
            | And _ as ts -> //TODO: something is completely wrong here. test result has (assert false) things...
                let ts = eatCondition ts
                List.map (fun t -> conds, t) ts
            | t -> [conds, t]
        let rec eat vars conds = function
            | QuantifierApplication(ForallQuantifier vars'::qs', body') -> eat (vars @ vars') conds (QuantifierApplication(qs', body'))
            | Or es ->
                let apps, rest = List.partition (function Apply(UserDefinedOperation(_, _, s), _) when s = BoolSort -> true | _ -> false) es
                let body = List.map SMTExpr.note rest
                match apps with
                | [] -> eat vars conds (SMTExpr.hence body SMTExpr.falsehood)
                | [app] -> eat vars conds (SMTExpr.hence body app)
                | _ -> failwithf $"Disjunction in clause head: %O{apps}"
            | Hence(cond, body) -> eat vars (eatCondition cond @ conds) body
            | And es -> List.collect (eat vars conds) es
//            | Apply(op, [app; body]) when op = equal_op BoolSort ->
//                let vars, body =
//                    match body with
//                    | Forall(varsBody, body) -> vars @ varsBody, body
//                    | _ -> vars, body
//                let te = VarEnv.create ctx vars
//                collector {
//                    let! bodyVars, bodyConditions, bodyResult = exprToRule te body
//                    let bodyResult = exprToAtoms bodyResult
//                    let! appVars, appConditions, appResult = exprToRule te app
//                    let r = finalRule vars bodyVars appVars (bodyResult @ bodyConditions @ appConditions) (getAppResult appResult)
//                    return TransformedCommand r
//                }
//            | Apply(ElementaryOperation("=", _, _), [app; body]) ->
//                let te = VarEnv.create ctx vars
//                collector {
//                    let! bodyVars, bodyConditions, bodyResult = exprToRule te body
//                    let! appVars, appConditions, appResult = exprToRule te app
//                    let r = finalRule vars bodyVars appVars (bodyConditions @ appConditions) (connectFunctionCallWithBody (exprToTerm appResult) bodyResult)
//                    return TransformedCommand r
//                }
            | app ->
                let tes = VarEnv(ctx).WithVars(vars), Map.empty
                collector {
                    let! appVars, appConditions, appResult = exprToRule tes app
                    let! bodyAddition = if assertsToQueries then exprToAtoms ctx assertsToQueries (SMTExpr.note appResult) else DNF.empty
                    let! headConds, head = if assertsToQueries then [[], SMTExpr.falsehood] else eatResultTerm [] appResult
                    let! bodyVars, bodyConditions, bodyResult = toRuleProduct tes (conds @ headConds)
                    let! bodyResult = List.map (exprToAtoms ctx assertsToQueries) bodyResult |> Disj.conj
                    let! headConstraints, head_atom = exprToAtoms ctx assertsToQueries head |> takeHead
                    let r = finalRule vars bodyVars appVars (headConstraints @ bodyAddition @ bodyResult @ bodyConditions @ appConditions) head_atom // TODO: not Bot
                    return TransformedCommand r
                }
        eat [] []

    let private dropWeakLiterals (ctx : Context) vars lemmaQs lemmaConds lemmaFOL =
        let dropWeak = function
            | Equal(t1, t2)
            | Distinct(t1, t2) as a when not (ADTExtensions.isGround t1 || ADTExtensions.isGround t2) -> a |> FOLAtom |> Some
            | _ -> None
        let dropWeak = function
            | FOLAtom a -> dropWeak a
            | f -> Some f
        match Simplification.simplifyConditional ctx.IsConstructor (Set.ofList vars) lemmaQs lemmaConds (fun unifier -> FOL.substituteWith unifier lemmaFOL) with
        | None -> []
        | Some (lemmaQs, lemmaConds, lemmaFOL) ->
        let strongLemma =
            match lemmaFOL with
            | FOLOr fs -> fs |> List.choose dropWeak |> FOL.folOr
            | FOLAtom _ as a -> dropWeak a |> Option.defaultValue (FOLAtom Bot)
            | f -> f
        [lemmaQs, (lemmaConds, strongLemma)]

    let private doubleNegateLemma (ctx : Context) = FOL.bind (ctx.Not >> List.map (FOLAtom >> FOL.folNot) >> FOL.folAnd)

    let private replaceDisequalWithDistinctInLemma (qs, (conds, lemma)) =
        let diseq = Map.find "distinct" Operations.elementaryOperations |> Operation.flipOperationKind
        let replaceAtom = function
            | Distinct(t1, t2) -> AApply(diseq, [t1; t2])
            | a -> a
        let conds = List.map replaceAtom conds
        let lemma = FOL.map replaceAtom lemma
        qs, (conds, lemma)

    let rec private defineCommandToDeclarations assertsToQueries ctx wereDefines = function
        | Definition(DefineFun df)
        | Definition(DefineFunRec df) ->
            let name, def = definitionToDeclaration df
            def :: definitionToAssertion ctx df, Set.add name wereDefines
        | Definition(DefineFunsRec dfs) ->
            let names, defs = List.map definitionToDeclaration dfs |> List.unzip
            defs @ List.collect (definitionToAssertion ctx) dfs, Set.union (Set.ofList names) wereDefines
        | Lemma(pred, vars, lemma) ->
            let tes = VarEnv(ctx).WithVars(vars), Map.empty
            collector {
                let! lemmaQs, lemmaConds, lemmaBody = exprToRule tes lemma
                let lemma = exprToAtoms ctx assertsToQueries lemmaBody
                let lemmaFOL = lemma |> DNF.toFOL
                let! lemmaQs, (lemmaConds, strongLemma) = dropWeakLiterals ctx vars lemmaQs lemmaConds lemmaFOL
                let bodyLemma : lemma = lemmaQs, (lemmaConds, strongLemma)
                let doubleNegatedLemma = doubleNegateLemma ctx strongLemma
                let headCube = Lemma.withFreshVariables(lemmaQs, (lemmaConds, doubleNegatedLemma))
                return LemmaCommand(pred, vars, bodyLemma, headCube)
            }, wereDefines
        | Assert e -> expressionToDeclarations assertsToQueries ctx e, wereDefines
        | Command c -> [OriginalCommand c], wereDefines

    let definesToDeclarations assertsToQueries commands =
        let commands, wereDefines = Context.typerMapFold (defineCommandToDeclarations assertsToQueries) Set.empty commands
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
        | And es -> es |> invertMatchesInExprList |> SMTExpr.ande
        | Or es -> es |> invertMatchesInExprList |> SMTExpr.ore
        | Not e -> e |> invertMatchesInExpr |> SMTExpr.note
        | Hence(a, b) -> Hence(invertMatchesInExpr a, invertMatchesInExpr b)
        | QuantifierApplication(qs, body) -> QuantifierApplication(qs, invertMatchesInExpr body)
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
        let commands = List.map (function Assert(Not(QuantifierApplication(ForallQuantifier _::_, _) as body)) -> Assert body | c -> c) commands
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
        let args = List.map Term.generateVariable args
        let ret = Term.generateVariable ret
        Rule.aerule args [ret] [] (relapply op args ret)

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
        | OriginalCommand(DeclareDatatype dt) ->
            let nc = ADTExtensions.adtDefinitionToRaw dt
            sortDeclaration dt :: constrDeclarations nc
            |> List.map OriginalCommand
        | OriginalCommand(DeclareDatatypes dts) ->
            List.map sortDeclaration dts @ List.collect constrDeclarations (ADTExtensions.adtDefinitionsToRaw dts)
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
        | Some (newSortName, _, _) -> FreeSort newSortName, an
        | None ->
            let newSortName = generateArraySortName s1 s2
            let newSort = FreeSort newSortName
            let selectOp = generateSelectOp newSortName newSort s1 s2
            let storeOp = generateStoreOp newSortName newSort s1 s2
            let arraySorts = Map.add originalSort (newSortName, selectOp, storeOp) arraySorts
            let originalSorts = Set.add originalSort originalSorts
            newSort, (arraySorts, originalSorts)

    let rec private mapSort arraySorts = function
        | ArraySort(s1, s2) as s ->
            let s1, arraySorts = mapSort arraySorts s1
            let s2, arraySorts = mapSort arraySorts s2
            addArraySortMapping arraySorts s s1 s2
        | s -> s, arraySorts

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
        let selectOpDeclarations = List.map Command.declareOp selectOps
        let storeOpDeclarations = List.map Command.declareOp storeOps
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
    type SubstituteFreeSortsWithNat (natSort, freeSorts) =
        inherit FormulaTraverser ()
        let mutable wasSubstituted = false
        
        member x.WasSubstituted = wasSubstituted
        
        override x.TraverseSort s = if Set.contains s freeSorts then wasSubstituted <- true; natSort else s
    
    let transformation freeSorts natSort (eqs, diseqs) commands =
        let x = SubstituteFreeSortsWithNat(natSort, Set.map FreeSort freeSorts)
        let substFreeSortsInCommand = function
            | OriginalCommand(DeclareSort s) when Set.contains s freeSorts -> None
            | c -> Some (x.TraverseTransformedCommand c)
        let commands = List.choose substFreeSortsInCommand commands
        let commands = List.map (SubstituteOperations(Map.empty, eqs, diseqs).SubstituteOperationsWithRelations) commands
        x.WasSubstituted, commands

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
        let lemma = FOL.folOr [FOL.substituteWith varsMap lemma; FOLAtom <| AApply(lemmaOp, ts)]
        let conds = List.map (Atom.substituteWith varsMap) conds
        lemma, conds, qs

    let private substitutePredicateCallWithLemmas pos lemmas ts =
        let substitutePredicateCallWithLemma (lemmaOp, vars, bl, hl) =
            let qs, (conds, lemma) = if pos then hl else bl
            callLemmaOn lemmaOp vars lemma conds qs ts
        let lemmaPieces, conds, qs = lemmas |> List.map substitutePredicateCallWithLemma |> List.unzip3
        let q = Quantifiers.combineMany qs
        FOL.folAnd lemmaPieces, List.concat conds, q

    let private mapAtom pos lemmasMap = function
        | AApply(op, ts) as a ->
            match Map.tryFind (Operation.opName op) lemmasMap with
            | Some lemmas -> substitutePredicateCallWithLemmas pos lemmas ts
            | None -> FOLAtom a, [], Quantifiers.empty
        | a -> FOLAtom a, [], Quantifiers.empty

    let private mapRule lemmasMap qs body head =
        let head, headConds, headQ = mapAtom true lemmasMap head
        let body, bodyConds, bodyQs = List.map (mapAtom false lemmasMap) body |> List.unzip3
        let body = List.map FOL.folNot (headConds::bodyConds |> List.concat |> List.map FOLAtom |> List.append body)
        let f = FOL.folOr (head::body)
        let q = Quantifiers.combineMany (qs :: headQ :: bodyQs)
        q, f

    let private mapCommand lemmasMap = function
        | OriginalCommand(DeclareFun(pred, _, _) as c) ->
            match Map.tryFind pred lemmasMap with
            | None -> [c]
            | Some lemmas -> lemmas |> List.map (fun (op, _, _, _) -> Command.declareOp op)
            |> List.map FOLOriginalCommand
        | OriginalCommand c -> [FOLOriginalCommand c]
        | TransformedCommand(Rule(qs, body, head)) -> mapRule lemmasMap qs body head |> folAssert |> Option.toList
        | TransformedCommand(Equivalence(qs,body,head)) ->
            let body = List.map FOLAtom body |> FOLAnd
            let head = FOLAtom head
            let e = FOLEq(body, head)
            folAssert(qs, e) |> Option.toList
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
    let private simplifyCommand (ctx : Context) = function
        | TransformedCommand(Rule(qs, body, head)) ->
            match Simplification.simplifyConditional ctx.IsConstructor Set.empty qs body (fun unifier -> Atom.substituteWith unifier head) with
            | None -> None
            | Some (qs, body, head) -> Some (TransformedCommand(Rule(qs, body, head)))
        | c -> Some c

    let simplify commands = Context.typerMap simplifyCommand commands |> List.choose id

let toClauses (options : transformOptions) commands =
    let commands = filterOutSMTCommands commands
    let commands = if options.tip then TIPFixes.applyTIPfix commands else commands
    let freeSorts = commands |> List.choose (function Command(DeclareSort(s)) -> Some s | _ -> None) |> Set.ofList
    let hornClauses, wereDefines = DefinitionsToDeclarations.definesToDeclarations options.tip commands
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
    elif options.tta_transform then
        let ttaClauses = TtaTransform.transform clausesWithPreamble
        {trCtx with commands = ttaClauses}
    else
        trCtx
