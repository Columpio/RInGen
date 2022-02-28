module RInGen.TtaTransform

open System.Collections.Generic
open FOLCommand

type private pattern =
     | Pattern of term list
     override x.ToString() =
         let (Pattern(pat)) = x
         pat |> List.map toString |> join ", "

type private AutomatonRecord(name : ident, init : operation, isFinal : operation, delta : operation, reach: operation) =
    member r.Name = name
    member r.Init = Term.apply0 init
    member r.IsFinal = Atom.apply1 isFinal
    member r.Delta = Term.apply delta
    member r.Reach = Atom.apply1 reach
    member r.Declarations = List.map (Command.declareOp >> FOLOriginalCommand) [init; isFinal; delta; reach]

type private Automaton(r : AutomatonRecord, tr) =
    member x.Record = r
    member x.Name = r.Name
    member x.Init = r.Init
    member x.IsFinal = r.IsFinal
    member x.Delta = r.Delta
    member x.Reach = r.Reach
    member x.Declarations = r.Declarations @ tr

module private Automaton =
    let fromSorts m stateSort name sortList =
        let initStateName = IdentGenerator.gensymp ("init_" + name)
        let isFinalName = IdentGenerator.gensymp ("isFinal_" + name)
        let deltaName = IdentGenerator.gensymp ("delta_" + name)
        let reachName = IdentGenerator.gensymp ("reach_" + name)
        let statesVec =
            let n = List.length sortList
            List.replicate (pown m n) stateSort

        let initState = Operation.makeElementaryOperationFromSorts initStateName [] stateSort
        let isFinal = Operation.makeElementaryRelationFromSorts isFinalName [stateSort]
        let delta = Operation.makeElementaryOperationFromSorts deltaName (sortList @ statesVec) stateSort
        let reach = Operation.makeElementaryRelationFromSorts reachName [stateSort]
        AutomatonRecord(name, initState, isFinal, delta, reach)

    let fromOperation m stateSort op =
        let name = Operation.opName op
        let sorts = Operation.argumentTypes op
        fromSorts m stateSort name sorts

    let fromPattern m stateSort (Pattern terms) =
        let sorts = terms |> List.map Term.typeOf
        fromSorts m stateSort (IdentGenerator.gensymp "pat") sorts

module MetaConstructor =
    let create name retSort = Operation.makeUserOperationFromSorts name [] retSort

    let isMetaConstructor = Operation.isUserOperation

    let toTerm = Operations.operationToIdent

type private state =
    | SVar of ident
    | CombinedState of operation list * state list // ``Delay'' states
    | AutomatonApply of AutomatonRecord * pattern
    | DeltaApply of AutomatonRecord * operation list * state list

    override x.ToString() =
        match x with
        | SVar i -> i
        | AutomatonApply(a, pat) -> $"%s{a.Name}[{pat}]"
        | CombinedState(constrs, states) ->
            let cs = constrs |> List.map toString |> join ", "
            let ss = states |> List.map toString |> join ", "
            $"""((%s{cs}), (%s{ss}))"""
        | DeltaApply(a, constrs, states) ->
            let cs = constrs |> List.map toString |> join ", "
            let ss = states |> List.map toString |> join ", "
            $"""delta%s{a.Name}(%s{cs}, %s{ss})"""

type private invariant =
    | Invariant of operation list * state list
    override x.ToString() =
        match x with
        | Invariant(freeConstrs, abstrValues) ->
            let freeConstrsStr = freeConstrs |> List.map toString |> join ", "
            $"""(({freeConstrsStr}), ({abstrValues |> List.map toString |> join ", "}))"""

module private Pattern =
    let collectFreeVars (Pattern pat) = Terms.collectFreeVars pat
    let collectFreeVarsCounter (Pattern pat) = Terms.collectFreeVarsCounter pat
    let generalizeVariables (Pattern pat) =
        let pat', vars2vars = Terms.generalizeVariables pat
        Pattern pat', vars2vars

    let extractFromAtom = Atom.tryGetArguments >> Option.map Pattern

    let matchPattern (Pattern termsPat) (Pattern termsInst) =
        let rec matchWith ((constrMap, varMap) as maps) (termPat, termInst) k =
            match termPat with
            | TApply(fPat, argsPat) ->
                match termInst with
                | TApply(fInst, argsInst) ->
                    match Map.tryFind fPat constrMap with
                    | Some f when f = fInst ->
                        matchListsWith maps (List.zip argsPat argsInst) k
                    | Some _ -> None
                    | None ->
                        let maps = Map.add fPat fInst constrMap, varMap
                        matchListsWith maps (List.zip argsPat argsInst) k
                | _ -> None
            | TIdent(idPat, sortPat) ->
                match Map.tryFind (idPat, sortPat) varMap with
                | Some t when t = termInst -> k maps
                | Some _ -> None
                | None -> k (constrMap, Map.add (idPat, sortPat) termInst varMap)
            | _ when termPat = termInst -> k maps
            | _ -> None
        and matchListsWith maps pairs k = List.kfoldk matchWith maps pairs k
        matchListsWith (Map.empty, Map.empty) (List.zip termsPat termsInst) Some

    let instantiate instantiator (Pattern pat) = Pattern(Terms.instantiate instantiator pat)
    let rewrite substConstrs instantiator (Pattern pat) = Pattern(Terms.rewrite substConstrs instantiator pat)

    let cutHeads (Pattern pat) =
//        if Terms.isBottoms pat then None else //TODO
        Terms.cutHeads pat

    let depth (Pattern pat) = List.max <| List.map Term.depth pat

    let collectVariableDepths (Pattern pat) =
        List.fold (Term.foldVarsWithDepth Map.add) Map.empty pat

module private State =
    let rec toTerm stateSort = function
        | SVar name -> TIdent(name, stateSort)
        | DeltaApply(record, constrs, states) ->
            let terms = List.map (toTerm stateSort) states
            let constrs = List.map MetaConstructor.toTerm constrs
            record.Delta(constrs @ terms)
        | _ -> __notImplemented__()

    let mapAutomatonApplies f =
        let rec mapPattern = function
            | SVar _ as v -> v
            | AutomatonApply(name, pattern) -> f name pattern
            | DeltaApply(name, constrs, states) -> DeltaApply(name, constrs, List.map mapPattern states)
            | CombinedState(constrs, states) -> CombinedState(constrs, List.map mapPattern states)
        mapPattern

    let foldAutomatonApplies f =
        let rec fold z = function
            | SVar _ -> z
            | AutomatonApply(name, pattern) -> f z name pattern
            | CombinedState(_, states)
            | DeltaApply(_, _, states) -> List.fold fold z states
        fold

    let mapFoldAutomatonApplies f =
        let rec mapFold z = function
            | SVar _ as v -> v, z
            | AutomatonApply(name, pattern) -> f z name pattern
            | DeltaApply(name, heads, states) ->
                let states, z = List.mapFold mapFold z states
                DeltaApply(name, heads, states), z
            | CombinedState(heads, states) ->
                let states, z = List.mapFold mapFold z states
                CombinedState(heads, states), z
        mapFold

    let freeConstructors =
        let rec freeConstructors free state =
            match state with
            | DeltaApply(_, constrs, states) ->
                List.fold freeConstructors (constrs |> List.filter MetaConstructor.isMetaConstructor |> Set.ofList |> Set.union free) states
            | _ -> free
        freeConstructors Set.empty >> Set.toList

    let instantiate instantiator = mapAutomatonApplies (fun name pat -> AutomatonApply(name, Pattern.instantiate instantiator pat))
    let rewrite substConstrs instantiator = mapAutomatonApplies (fun name pat -> AutomatonApply(name, Pattern.rewrite substConstrs instantiator pat))

    let private unfoldAutomatonApplyGeneric mapChild =
        let bottomize tss =
            let N = List.map List.length tss |> List.max
            let padWithBottoms ts =
                let P = N - List.length ts
                if P = 0 then ts else
                ts @ List.replicate P (TConst("bot", ADTSort "Any")) //TODO: Term.Bottom
            List.map padWithBottoms tss

        let unfoldAutomatonApply name pattern =
            match Pattern.cutHeads pattern with
            | Some(heads, bodies) ->
                let bodies = bottomize bodies
                let states = List.product bodies |> List.map (fun pat -> AutomatonApply(name, Pattern pat))
                let states = List.map mapChild states
                DeltaApply(name, heads, states)
            | None -> AutomatonApply(name, pattern)
        mapAutomatonApplies unfoldAutomatonApply

    let unfoldAutomatonApplyOnce = unfoldAutomatonApplyGeneric id
    let rec unfoldAutomatonApplyRec state = unfoldAutomatonApplyGeneric unfoldAutomatonApplyRec state

    let freeVars = foldAutomatonApplies (fun free _ -> Pattern.collectFreeVars >> Set.ofList >> Set.union free) Set.empty

    let abstractAutomatonApplies s =
        let vars2states = Dictionary<_, _>()
        let states2vars = Dictionary<_, _>()
        let helper name pat =
            let a = AutomatonApply(name, pat)
            match Dictionary.tryFind a states2vars with
            | Some ident -> SVar ident
            | None ->
                let freshName = IdentGenerator.gensym ()
                vars2states.Add(freshName, a)
                states2vars.Add(a, freshName)
                SVar freshName
        mapAutomatonApplies helper s, (vars2states, states2vars)

module private Invariant =
    let fromConstructorsAndStates freeConstrs states =
        Invariant(freeConstrs, states)

    let private mapEachState f (Invariant(freeConstrs, states)) = Invariant(freeConstrs, List.map f states)

    let instantiate instantiator = mapEachState (State.instantiate instantiator)

    let mapAutomatonApplies f = mapEachState (State.mapAutomatonApplies f)

    let unfoldAutomatonApplyRec = mapEachState State.unfoldAutomatonApplyRec

    let private matchAutomatonApplyStates statePattern stateInstance =
        match statePattern, stateInstance with
        | AutomatonApply(namePat, termsPat), AutomatonApply(nameInst, termsInst) ->
            if namePat = nameInst then Pattern.matchPattern termsPat termsInst else None
        | _ -> __unreachable__()

    let rewrite state (rewriteFromState, Invariant(rewriteToConstrs, rewriteToStates)) =
        let rec rewrite = function
            | AutomatonApply _ as a ->
                match matchAutomatonApplyStates rewriteFromState a with
                | Some(substConstrs, substStates) ->
                    let constrs' = List.instantiate substConstrs rewriteToConstrs
                    let states' = List.map (State.rewrite substConstrs substStates) rewriteToStates
                    CombinedState(constrs', states')
                | None -> a
            | DeltaApply(name, constrs, states) -> DeltaApply(name, constrs, List.map rewrite states)
            | _ -> __notImplemented__()
        rewrite state

module private PatternAutomatonGenerator =
    let private linearInstantiator width pattern =
        let var2depth = Pattern.collectVariableDepths pattern
        let patDepth = Pattern.depth pattern
        var2depth |> Map.map (fun v depth -> if patDepth = depth then Term.generateVariableWithPrefix v else Term.falsehood) //TODO: Term.mkFullTree width (patDepth - depth))

    let private instantiate instantiator A B =
        let A' = State.instantiate instantiator A
        let B' = State.instantiate instantiator B
        let A'' = State.unfoldAutomatonApplyRec A'
        A'', B'

    let private finalStatesAndInvariant A B =
        // returns $"""Fb := {{ (({freeConstrsStr}), ({abstrVars |> List.map toString |> join ", "})) |{"\n\t"}{abstrState} \in Fa }}"""
        let abstrState, (abstrVarsMap, _) = State.abstractAutomatonApplies A
        let abstrVars = abstrVarsMap |> Dictionary.toList |> List.map fst
        let freeConstrs = State.freeConstructors abstrState
        let inv = Invariant.fromConstructorsAndStates freeConstrs (List.map (Dictionary.findOrApply SVar abstrVarsMap) abstrVars)
        (freeConstrs, abstrVars, abstrState), inv

    let private inductiveUnfoldings width B invariantA =
        let freeVars = State.freeVars B |> Set.toList
        let instantiator=
            freeVars
            |> List.map (fun ident -> ident, Term.falsehood) //TODO: Term.mkFullTree width 1)
            |> Map.ofList
        let B' = State.instantiate instantiator B
        let B'' = State.unfoldAutomatonApplyOnce B'
        let sideB = Invariant.rewrite B'' (B, invariantA)

        let invariantA' = Invariant.instantiate instantiator invariantA
        let invariantA'' = Invariant.unfoldAutomatonApplyRec invariantA'
        sideB, invariantA''

    let private inductionSchema leftSide rightSide =
        let abstrLeftSide, (_, state2vars) = State.abstractAutomatonApplies leftSide
        let abstrRightSide =
            let mapper name pat =
                let a = AutomatonApply(name, pat)
                match Dictionary.tryFind a state2vars with
                | Some ident -> SVar ident
                | None -> a
            Invariant.mapAutomatonApplies mapper rightSide
        abstrLeftSide, abstrRightSide

    let private automatonFromDeltaAndFinals stateSort (patternRec : AutomatonRecord) (baseAutomaton : AutomatonRecord) delta (finalConstrs, finalIdents, finalState) =
        // """Fb(freeConstrs, abstrVars) <=> Fa(abstrState)"""
        let finalDecls =
            let r = baseAutomaton.IsFinal(State.toTerm stateSort finalState)
            let Delay = function
                | [], [x] -> TIdent(x, stateSort)
                | _ -> __notImplemented__()
            let l = patternRec.IsFinal(Delay(finalConstrs, finalIdents))
            clAEquivalence [l] r
        let decls = finalDecls :: []
        Automaton(patternRec, decls)

    let generatePatternAutomaton width stateSort (baseAutomaton : Automaton) pattern =
        let generalizedPattern, vars2vars = Pattern.generalizeVariables pattern
        let newVars = Map.toList vars2vars |> List.map fst |> List.unique
        let instantiator = linearInstantiator width generalizedPattern
        let A = AutomatonApply(baseAutomaton.Record, generalizedPattern)
        let patternRec, B =
            let pattern' = pattern |> Pattern.collectFreeVars |> SortedVars.sort |> List.map TIdent |> Pattern
            let record = Automaton.fromPattern width stateSort pattern'
            record, AutomatonApply(record, pattern')
        let A, B = instantiate instantiator A B
        let finalStates, invariantA = finalStatesAndInvariant A B
        let leftSide, rightSide = inductiveUnfoldings width B invariantA
        let delta = inductionSchema leftSide rightSide
        let patAutomaton = automatonFromDeltaAndFinals stateSort baseAutomaton.Record patternRec delta finalStates
//        let equalityAutomaton = buildEqualityAutomaton newVars
//        let intersectionAutomaton = intersect equalityAutomaton patAutomaton
//        let prAutomaton = proj newVars intersectionAutomaton //TODO: do we really need it?
//        intersectionAutomaton
        patAutomaton

type private ToTTATraverser(m : int) =
    let stateSortName = IdentGenerator.gensymp "State"
    let stateSort = FreeSort stateSortName

    let equal s = Atom.apply2 (Operations.equal_op s)
    let equalStates = equal stateSort

    let botSymbols = Dictionary<_, _>()
    let patternAutomata = Dictionary<_, _>()
    let products = Dictionary<_, _>()

    let equalityNames = Dictionary<_, _>()
    let disequalityNames = Dictionary<_, _>()
    let applicationNames = Dictionary<_, _>()

    let equalities = Dictionary<_, _>()
    let disequalities = Dictionary<_, _>()
    let applications = Dictionary<_, _>()

    member private x.getBotSymbol sort =
        Dictionary.getOrInitWith sort botSymbols (fun () -> IdentGenerator.gensymp <| Sort.sortToFlatString sort + "_bot")

    member private x.getEqRelName s arity =
        Dictionary.getOrInitWith (s, arity) equalityNames (fun () -> IdentGenerator.gensymp $"eq_{s}_{arity}")

    member private x.getDiseqRelName s = //TODO: no need after diseq transform
        "diseq" + s.ToString()

    member private x.GenerateEqualityAutomaton s arity =
        let eqRelName = x.getEqRelName s arity
        let eqRec = Automaton.fromSorts m stateSort eqRelName (List.replicate arity s)

        let initAxiom = clAFact(eqRec.IsFinal eqRec.Init)
        let deltaAxiom =
            let qTerms = Terms.generateNVariablesOfSort (pown m arity) stateSort
            let constrTerms =
                let fTerm = Term.generateVariable s
                List.replicate arity fTerm
            let l = eqRec.IsFinal(eqRec.Delta(constrTerms @ qTerms))
            let r =
                let qTerms = Array.ofList qTerms
                let qDiag = List.init m (fun i -> qTerms.[i*(m+1)])
                List.map eqRec.IsFinal qDiag
            clAEquivalence r l
        Automaton(eqRec, [initAxiom; deltaAxiom])

    member private x.GenerateDisqualityAutomaton s =
        __notImplemented__()

    member private x.GetOrAddEqualityAutomaton ts =
        let s = List.head ts |> Term.typeOf
        let n = List.length ts
        let baseAutomaton = Dictionary.getOrInitWith (s, n) equalities (fun () -> x.GenerateEqualityAutomaton s n)
        x.GetOrAddPatternAutomaton baseAutomaton (Pattern ts)

    member private x.GetOrAddDisequalityAutomaton y z =
        let s = Term.typeOf y
        let baseAutomaton = Dictionary.getOrInitWith s disequalities (fun () -> x.GenerateDisqualityAutomaton s)
        x.GetOrAddPatternAutomaton baseAutomaton (Pattern [y; z])

    member private x.GetOrAddApplicationAutomaton op xs =
        let baseAutomaton = x.GetOrAddOperationAutomaton op
        x.GetOrAddPatternAutomaton baseAutomaton (Pattern xs)

    member private x.TraverseDatatype (sName, xs) =
        let s = ADTSort sName
        let constructors = x.getBotSymbol s :: List.map (fst3 >> Operation.opName) xs
        let constrDecls = List.map (fun name -> DeclareConst(name, s)) constructors
        List.map FOLOriginalCommand (DeclareSort(sName) :: constrDecls)

    member private x.GetOrAddPatternAutomaton baseAutomaton (Pattern pattern) =
        let vars = Terms.collectFreeVars pattern |> List.sortWith SortedVar.compare
        let renameMap = List.mapi (fun i (_, s as v) -> (v, TIdent ($"x_{i}", s))) vars |> Map.ofList
        let pattern = List.map (Term.substituteWith renameMap) pattern
        Dictionary.getOrInitWith pattern patternAutomata (fun () ->
            PatternAutomatonGenerator.generatePatternAutomaton m stateSort baseAutomaton (Pattern pattern))

    member private x.Product terms =
        assert(List.forall (fun t -> Term.typeOf t = stateSort) terms)
        let n = List.length terms
        let generateProdOperation () =
            let prodName = IdentGenerator.gensymp "prod"
            Operation.makeElementaryOperationFromSorts prodName (List.replicate n stateSort) stateSort

        let op = Dictionary.getOrInitWith n products generateProdOperation
        Term.apply op terms

    member private x.GenerateAtomAutomaton a =
        match a with
        | Top | Bot -> None
        | Equal(y, z) -> Some(a, x.GetOrAddEqualityAutomaton [y; z])
        | Distinct(y, z) -> Some(a, x.GetOrAddDisequalityAutomaton y z)
        | AApply(op, xs) -> Some(a, x.GetOrAddApplicationAutomaton op xs)

    member private x.TraverseRule (Rule(_, body, head) as rule) =
        let pairHeadAndBody = List.cons
        let unpairHeadAndBody = List.uncons
        let atoms, patAutomata = List.unzip <| List.choose x.GenerateAtomAutomaton (pairHeadAndBody head body)

        let clauseName = IdentGenerator.gensymp "clause"
        let clauseVars = Atoms.collectFreeVars atoms |> SortedVars.sort
        let cRecord = Automaton.fromSorts m stateSort clauseName (List.map snd clauseVars)

        // process rule
        let atomsVars = atoms |> List.map Atom.collectFreeVars |> List.map SortedVars.sort
        let clauseVarsTerms = clauseVars |> List.map TIdent

        let initAxiom =
            let l = cRecord.Init
            let inits = patAutomata |> List.map (fun (r : Automaton) -> r.Init)
            let r = x.Product inits
            clAFact (equalStates l r)
        let deltaAxiom =
            let stateTerms = List.map (fun vars -> (Terms.generateNVariablesOfSort (pown m (List.length vars)) stateSort)) atomsVars
            let atomsTerms = List.map (List.map TIdent) atomsVars
            let rs = List.map3 (fun (r : Automaton) vs s -> r.Delta(vs @ s)) patAutomata atomsTerms stateTerms
            let r = x.Product rs
            let l =
                // helper functions
                let genQMask aVars = List.map (fun v -> List.contains v aVars) clauseVars
                let applyMask combination mask =
                    List.zip combination mask
                 |> List.filter snd
                 |> List.rev
                 |> List.mapi (fun i (el,_) -> el * (pown m i))
                 |> List.sum

                (*
                    masks ~ used ADT variables in atom
                    example: if clauseVars= [f1; f2; f3], atomVars=[f1;f3] then mask=[T; F; T]
                *)
                let posMasks = List.map genQMask atomsVars
                let combinations = Numbers.allNumbersBaseM (List.length clauseVars) m
                (*
                    generate from [q0*; q1*] (n=1) -> [q0*; q0*; q1*; q1*] which can be used in prod
                    with [q00; q01; q10; q11] (n=2)
                *)
                let statePositions = List.map (fun c -> List.map (applyMask c) posMasks) combinations
                let stateTerms = statePositions |> List.map (fun positions -> List.map2 List.item positions stateTerms)
                let lStates = List.map x.Product stateTerms
                cRecord.Delta(clauseVarsTerms @ lStates)
            clAFact (equalStates l r)
        let finalAxiom =
            let stateTerms = Terms.generateNVariablesOfSort (List.length patAutomata) stateSort
            let li = x.Product stateTerms
            let l = FOLAtom <| cRecord.IsFinal li
            let rs = List.map2 (fun (r : Automaton) -> r.IsFinal >> FOLAtom) patAutomata stateTerms
            let rs =
                match head with
                | Bot -> rs
                | _ -> // head isFinal is negated
                    let r, rs = unpairHeadAndBody rs
                    FOLNot r :: rs
            clAEquivalenceFromFOL rs l
        let reachInit =
            clAFact (cRecord.Reach cRecord.Init)
        let reachDelta =
            let qTerms = Terms.generateNVariablesOfSort (pown m (List.length clauseVarsTerms)) stateSort
            let l = List.map cRecord.Reach qTerms
            let r = cRecord.Reach(cRecord.Delta(clauseVarsTerms @ qTerms))
            clARule l r
        let condition = // negation of the clause: each reachable is not final
            let qTerm = Term.generateVariable stateSort
            clARule [cRecord.Reach qTerm; cRecord.IsFinal qTerm] Bot
        let tCommands = [initAxiom; deltaAxiom; finalAxiom; reachInit; reachDelta; condition]

        cRecord.Declarations @ tCommands

    member private x.GenerateAutomaton name args = Automaton.fromSorts m stateSort name args

    member private x.GetOrAddOperationAutomaton op =
        Dictionary.getOrInitWith op applications (fun () -> Automaton(Automaton.fromOperation m stateSort op, []))

    member private x.GenerateProductDeclarations () =
        products |> Dictionary.toList |> List.collect (fun (_, op) -> (Automaton.fromOperation m stateSort op).Declarations)

    member private x.GeneratePatternDeclarations () =
        patternAutomata |> Dictionary.toList |> List.collect (fun (_, a) -> a.Declarations)

    member private x.TraverseCommand = function
        | DeclareFun(name, args, BoolSort) ->
            let op = Operation.makeUserRelationFromSorts name args
            (x.GetOrAddOperationAutomaton op).Declarations
        | DeclareDatatype dt -> x.TraverseDatatype dt
        | DeclareDatatypes dts -> List.collect x.TraverseDatatype dts
        | c -> [FOLOriginalCommand c]

    member private x.TraverseTransformedCommand = function
        | OriginalCommand o -> x.TraverseCommand o
        | TransformedCommand rule -> x.TraverseRule rule
        | LemmaCommand _ -> __unreachable__()

    member x.TraverseCommands commands =
        let header = FOLOriginalCommand(DeclareSort(stateSortName))
        let commands' = List.collect x.TraverseTransformedCommand commands
        let prodDecls = x.GenerateProductDeclarations ()
        let patternDecls = x.GeneratePatternDeclarations ()
        header :: prodDecls @ patternDecls @ commands'

let transform (commands : 'a list) =
    let commands = [commands.[0]; commands.[1]; commands.[2]; commands.[3]; commands.[4]; commands.[11]; commands.[12]; commands.[13]; commands.[14]]
    let maxConstructorWidth = List.max <| List.map (function OriginalCommand c -> Command.maxConstructorArity c | _ -> Datatype.noConstructorArity) commands
    let processer = ToTTATraverser(maxConstructorWidth)
    processer.TraverseCommands(commands)
