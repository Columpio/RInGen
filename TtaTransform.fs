module RInGen.TtaTransform

open System.Collections.Generic
open System.Diagnostics
open SMTLIB2
open FOLCommand

let adtConstructorSortName = IdentGenerator.gensymp "adtConstr"
let adtConstructorSort = ADTSort adtConstructorSortName
let adtToConstrSort s = adtConstructorSort
//let adtToConstrSort s = s

type LinearIndex(strategyWidth, strategyHeight) =
    let mutable i = -1

    member x.HasNext() = i + 1 < strategyWidth

    member x.Increment() =
        i <- i + 1

    member x.SetAtCurrent(arr : 'a array array, value : 'a) =
        arr.[i] <- Array.init strategyHeight (fun _ -> value)

    override x.ToString() = $"({i}, *)"

type strategy = (int * int) list list

type StrategyBuilder(width, vars, aloud) =
    let aloud = aloud
    let width = width
    let vars = vars
    let fullConvolution =
        List.init vars (fun i -> List.init width (fun j -> (i, j))) // for 2 2 gives [[(0, 0); (0, 1)]; [(1, 0); (1; 1)]]
        |> List.product
    let fullConvolution = Seq.map List.toArray fullConvolution |> Array.ofSeq
    let strategyWidth, strategyHeight = pown width vars, vars
    let mask = Array.init strategyWidth (fun _ -> Array.init strategyHeight (fun _ -> true))

    let droppedElementPointer = LinearIndex(strategyWidth, strategyHeight)

    member private x.ApplyStrategy (strategy : strategy) (xss : 'a list list) =
        // List.length xss <= vars
        // for each i, List.length xss[i] = width
        // Ex: xss = [[A; B]; [C; D]], strategy = (full convolution) = [[(0, 0); (1, 0)]; [(0, 0); (1, 1)]; [(0, 1); (1, 0)]; [(0, 1); (1, 1)]]
        // Result: [[A; C]; [A; D]; [B; C]; [B; D]]
        // Ex: xss = [[A; B]] -> [[A]; [B]], but we have [[A]; [A]]
        let totalSize = List.length xss
        let strategy =
            if totalSize < vars then
                let modulo = pown width (vars - totalSize)
                strategy |> List.take modulo
            else
                strategy
        strategy
        |> List.map (List.choose (fun (i, j) -> if i < totalSize then Some(xss.[i].[j]) else None))

    member x.Build() =
        let strategy =
            Seq.map2 (fun strategyLine maskLine -> Seq.zip strategyLine maskLine |> Seq.choose (fun (e, b) -> if b then Some e else None) |> List.ofSeq) fullConvolution mask
            |> List.ofSeq
        x.ApplyStrategy strategy

    member x.IsReducible() = droppedElementPointer.HasNext()

    member x.ImproveCurrentStrategy() =
        droppedElementPointer.Increment()
        droppedElementPointer.SetAtCurrent(mask, false)
        if aloud then
            printf $"Trying to drop {droppedElementPointer}"

    member x.BacktrackStrategy() =
        droppedElementPointer.SetAtCurrent(mask, true)

type pattern =
     | Pattern of term list
     override x.ToString() =
         let (Pattern(pat)) = x
         pat |> List.map toString |> join ", "

type AutomatonRecord(name : ident, init : operation, isFinal : operation, delta : operation, reach: operation) =
    member r.Name = name
    member r.Init = Term.apply0 init
    member r.IsFinal = Atom.apply1 isFinal
    member r.Delta = delta
    member r.Reach = Atom.apply1 reach
    member r.Declarations = List.map (Command.declareOp >> FOLOriginalCommand) [init; isFinal; delta; reach]
    member r.isEmpty =
        match delta with
        | ElementaryOperation(_, xs, _) | UserDefinedOperation(_, xs, _) -> List.length xs = 1

type Automaton(r : AutomatonRecord, tr) =
    member x.Record = r
    member x.Name = r.Name
    member x.Init = r.Init
    member x.IsFinal = r.IsFinal
    member x.Delta = r.Delta
    member x.Reach = r.Reach
    member x.Declarations = r.Declarations @ tr

module Automaton =
    let isEmpty (aut: Automaton) = aut.Record.isEmpty
    let notEmpty (aut: Automaton) = not aut.Record.isEmpty
    
    let fromSorts m strategy stateSort name sortList =
        let sortList = List.map adtToConstrSort sortList
        let initStateName = IdentGenerator.gensymp ("init_" + name)
        let isFinalName = IdentGenerator.gensymp ("isFinal_" + name)
        let deltaName = IdentGenerator.gensymp ("delta_" + name)
        let reachName = IdentGenerator.gensymp ("reach_" + name)
        let statesVec =
            let dummy = TConst("dummy", stateSort)
            let childDummies = List.map (fun _ -> List.replicate m dummy) sortList
            childDummies
            |> strategy
            |> List.choose (fun l -> if List.isEmpty l then None else Some l)
            |> List.map (fun _ -> stateSort)

        let initState = Operation.makeElementaryOperationFromSorts initStateName [] stateSort
        let isFinal = Operation.makeElementaryRelationFromSorts isFinalName [stateSort]
        let delta = Operation.makeElementaryOperationFromSorts deltaName (sortList @ statesVec) stateSort
        let reach = Operation.makeElementaryRelationFromSorts reachName [stateSort]
        AutomatonRecord(name, initState, isFinal, delta, reach)

    let fromOperation m strategy stateSort op =
        let name = Operation.opName op
        let sorts = Operation.argumentTypes op
        fromSorts m strategy stateSort name sorts

    let fromPattern m strategy stateSort (Pattern terms) =
        let sorts = terms |> List.map Term.typeOf
        fromSorts m strategy stateSort (IdentGenerator.gensymp "pat") sorts

module MetaConstructor =
    let create name retSort = Operation.makeUserOperationFromSorts name [] retSort

    let generate prefix retSort = create (IdentGenerator.gensymp prefix) retSort

    let isMetaConstructor = Operation.isUserOperation

    let toTerm op = if isMetaConstructor op then Operations.operationToIdent op else Term.apply0 op

type private state =
    | SInit
    | SVar of ident
    | CombinedState of operation list * state list // ``Delay'' states
    | AutomatonApply of operation * pattern // Operation is automaton delta
    | DeltaApply of operation * operation list * state list // Operation is automaton delta

    override x.ToString() =
        match x with
        | SInit -> "init"
        | SVar i -> i
        | AutomatonApply(a, pat) -> $"{a}[{pat}]"
        | CombinedState(constrs, states) ->
            let cs = constrs |> List.map toString |> join ", "
            let ss = states |> List.map toString |> join ", "
            $"""((%s{cs}), (%s{ss}))"""
        | DeltaApply(a, constrs, states) ->
            let cs = constrs |> List.map toString |> join ", "
            let ss = states |> List.map toString |> join ", "
            $"""delta_{a}(%s{cs}, %s{ss})"""

type private invariant =
    | Invariant of operation list * state list
    override x.ToString() =
        match x with
        | Invariant(freeConstrs, abstrValues) ->
            let freeConstrsStr = freeConstrs |> List.map toString |> join ", "
            $"""(({freeConstrsStr}), ({abstrValues |> List.map toString |> join ", "}))"""

module private Pattern =
    let isEmpty (Pattern pat) = (pat = [])
    let length (Pattern pat) = Terms.length pat 
    let isBottoms tester (Pattern pat) = List.forall tester pat
    let collectFreeVars (Pattern pat) = Terms.collectFreeVars pat
    let collectFreeVarsCounter (Pattern pat) = Terms.collectFreeVarsCounter pat
    let linearizeVariables (Pattern pat) =
        let pat', vars2vars = Terms.linearizeVariables pat
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

    let cutHeads isBottom (Pattern pat) =
        match Terms.cutHeads pat with
        | Some(ops, _) when List.forall isBottom ops -> None
        | o -> o

    let depth (Pattern pat) = List.max <| List.map Term.depth pat
    let numVars pat = collectFreeVars pat |> List.length

    let collectVariableDepths (Pattern pat) =
        List.fold (Term.foldVarsWithDepth Map.add) Map.empty pat

module private State =
    let mapAutomatonApplies f =
        let rec mapPattern = function
            | SInit -> SInit
            | SVar _ as v -> v
            | AutomatonApply(name, pattern) -> f name pattern
            | DeltaApply(name, constrs, states) -> DeltaApply(name, constrs, List.map mapPattern states)
            | CombinedState(constrs, states) -> CombinedState(constrs, List.map mapPattern states)
        mapPattern

    let foldAutomatonApplies f =
        let rec fold z = function
            | SInit | SVar _ -> z
            | AutomatonApply(name, pattern) -> f z name pattern
            | CombinedState(_, states)
            | DeltaApply(_, _, states) -> List.fold fold z states
        fold

    let mapFoldAutomatonApplies f =
        let rec mapFold z = function
            | SInit -> SInit, z
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

    let private unfoldAutomatonApplyGeneric isBottom bottomize strategy mapChild =
        let unfoldAutomatonApply name pattern =
            match Pattern.cutHeads isBottom pattern with
            | Some(heads, bodies) ->
                let bodies = List.map2 bottomize heads bodies
//                let states = strategy bodies |> List.map (fun pat -> AutomatonApply(name, Pattern pat))
                let states = strategy bodies |> List.choose (fun pat -> if pat = [] then None else Some <| AutomatonApply(name, Pattern pat))
                let states = List.map mapChild states
                DeltaApply(name, heads, states)
            | None ->
                match pattern with
                | Pattern(pat) ->
                    if List.exists Term.isIdent pat then AutomatonApply(name, pattern) else SInit
        mapAutomatonApplies unfoldAutomatonApply

    let unfoldAutomatonApplyOnce isBottom bottomize strategy = unfoldAutomatonApplyGeneric isBottom bottomize strategy id
    let rec unfoldAutomatonApplyRec isBottom bottomize strategy state =
        unfoldAutomatonApplyGeneric isBottom bottomize strategy (unfoldAutomatonApplyRec isBottom bottomize strategy) state

    let freeVars = foldAutomatonApplies (fun free _ -> Pattern.collectFreeVars >> Set.ofList >> Set.union free) Set.empty

    let abstractAutomatonApplies s =
        let vars2states = Dictionary<_, _>()
        let states2vars = Dictionary<_, _>()
        let helper name pat =
            let a = AutomatonApply(name, pat)
            match Dictionary.tryFind a states2vars with
            | Some ident -> SVar ident
            | None ->
                if Pattern.isEmpty pat then SInit else
                let freshName = IdentGenerator.gensym ()
                vars2states.Add(freshName, a)
                states2vars.Add(a, freshName)
                SVar freshName
        mapAutomatonApplies helper s, (vars2states, states2vars)

    let collectAutomatonApplies = foldAutomatonApplies (fun states name pat -> Set.add (AutomatonApply(name, pat)) states) Set.empty

    let isVarSubset left right =
        // left \subseteq right <=> left \ right = \emptyset
        let callsLeft = freeVars left
        let callsRight = freeVars right
        let callsDiff = Set.difference callsLeft callsRight
        Set.isEmpty callsDiff

module private Invariant =
    let fromConstructorsAndStates freeConstrs states =
        Invariant(freeConstrs, states)

    let private mapEachState f (Invariant(freeConstrs, states)) = Invariant(freeConstrs, List.map f states)

    let instantiate instantiator = mapEachState (State.instantiate instantiator)

    let mapAutomatonApplies f = mapEachState (State.mapAutomatonApplies f)

    let unfoldAutomatonApplyRec isBottom bottomize strategy = mapEachState (State.unfoldAutomatonApplyRec isBottom bottomize strategy)

    let private matchAutomatonApplyStates statePattern stateInstance =
        match statePattern, stateInstance with
        | AutomatonApply(namePat, termsPat), AutomatonApply(nameInst, termsInst) ->
            if namePat = nameInst then Pattern.matchPattern termsPat termsInst else None
        | _ -> __unreachable__()

    let rewrite state (rewriteFromState, Invariant(rewriteToConstrs, rewriteToStates)) =
        let rec rewrite = function
            | SInit -> SInit
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

    let collectAutomatonApplies (Invariant(_, states)) = states |> List.map State.collectAutomatonApplies |> Set.unionMany
    
    let difference inv state =
        // {b1, .., bk} \subseteq {a1, .., al} <=> (b1 = a1 /\ ... /\ b1 = al) \/ ... \/ (bk = a1 /\ ... /\ bk = al)
        let callsLeft = State.collectAutomatonApplies state
        let callsRight = collectAutomatonApplies inv
        let callsDiff = Set.difference callsRight callsLeft
        callsDiff

module private PatternAutomatonGenerator =
    let private mkApplyNary N prefix sort init = TApply(MetaConstructor.generate prefix sort, List.init N init)

    let mkFullTree width height sort = //TODO: this is not general enough! works only for single sort ADTs
        let rec iter height =
            if height <= 0 then Term.generateVariable (adtToConstrSort sort)
                           else mkApplyNary width "f" (adtToConstrSort sort) (fun _ -> iter (height - 1))
        iter height

    let linearInstantiator width pattern =
        let var2depth = Pattern.collectVariableDepths pattern
        let patDepth = Pattern.depth pattern
        var2depth |> Map.map (fun (_, s) depth -> mkFullTree width (patDepth - depth) s)

    let instantiate isBottom bottomize strategy instantiator A B =
        let A' = State.instantiate instantiator A
        let B' = State.instantiate instantiator B
        let A'' = State.unfoldAutomatonApplyRec isBottom bottomize strategy A'
        A'', B'

    let finalStatesAndInvariant A =
        // returns $"""Fb := {{ (({freeConstrsStr}), ({abstrVars |> List.map toString |> join ", "})) |{"\n\t"}{abstrState} \in Fa }}"""
        let abstrState, (abstrVarsMap, _) = State.abstractAutomatonApplies A
        let abstrVars = abstrVarsMap |> Dictionary.toList |> List.map fst
        let freeConstrs = State.freeConstructors abstrState
        let inv = Invariant.fromConstructorsAndStates freeConstrs (List.map (Dictionary.findOrApply SVar abstrVarsMap) abstrVars)
        (freeConstrs, abstrVars, abstrState), inv

    let inductiveUnfoldings isBottom bottomize strategy width B invariantA =
        let freeVars = State.freeVars B |> Set.toList
        let instantiator=
            freeVars
            |> List.map (fun (_, s as ident) -> ident, mkFullTree width 1 s)
            |> Map.ofList
        let B' = State.instantiate instantiator B
        let B'' = State.unfoldAutomatonApplyOnce isBottom bottomize strategy B'
        let sideB = Invariant.rewrite B'' (B, invariantA)

        let invariantA' = Invariant.instantiate instantiator invariantA
        let invariantA'' = Invariant.unfoldAutomatonApplyRec isBottom bottomize strategy invariantA'
        sideB, invariantA''

    let inductionSchema leftSide rightSide =
        let abstrLeftSide, (_, state2vars) = State.abstractAutomatonApplies leftSide
        let abstrRightSide =
            let mapper name pat =
                let a = AutomatonApply(name, pat)
                match Dictionary.tryFind a state2vars with
                | Some ident -> SVar ident
                | None -> a
            Invariant.mapAutomatonApplies mapper rightSide
        abstrLeftSide, abstrRightSide

    let strategyIsEmpty isBottom bottomize m strategy A =
        let prepareInduction state =
            let freeVars = State.freeVars state |> Set.toList
            freeVars
            |> List.map (fun (ident, sort) -> (ident, sort), mkFullTree m 1 sort)
            |> Map.ofList        
        let instantiator = prepareInduction A
        let instA = State.instantiate instantiator A
        let unfoldedA = State.unfoldAutomatonApplyOnce isBottom bottomize strategy instA
        not <| State.isVarSubset instA unfoldedA

type ToTTATraverser(m : int) =
    let fcStrategy = List.product
    let stateSortName = IdentGenerator.gensymp "State"
    let stateSort = FreeSort stateSortName

    let equal s = Atom.apply2 (Operations.equal_op s)
    let equalStates = equal stateSort

    let patternAutomata = Dictionary<_, _>()

    let botSymbols = Dictionary<_, _>()
    let products = Dictionary<_, _>()
    let delays = Dictionary<_, _>()

    let equalityNames = Dictionary<_, _>()

    let equalities = Dictionary<_, _>()
    let applications = Dictionary<_, _>()

    let dumpOpDictionary opDict =
        opDict |> Dictionary.toList |> List.map (fun (_, op) -> FOLOriginalCommand(Command.declareOp op))

    member private x.getBotSymbol sort =
        Dictionary.getOrInitWith sort botSymbols (fun () -> IdentGenerator.gensymp <| Sort.sortToFlatString sort + "_bot")
    member private x.getBottom sort =
        Term.apply0 <| Operation.makeElementaryOperationFromSorts (x.getBotSymbol sort) [] sort

    member private x.getEqRelName s arity =
        Dictionary.getOrInitWith (s, arity) equalityNames (fun () -> IdentGenerator.gensymp $"eq_{s}_{arity}")

    member private x.GenerateEqualityAutomaton s arity =
        let eqRelName = x.getEqRelName s arity
        let eqRec = Automaton.fromSorts m fcStrategy stateSort eqRelName (List.replicate arity s)

        let initAxiom = clAFact(eqRec.IsFinal eqRec.Init)

        let deltaAxiom =
            let qTerms = Terms.generateNVariablesOfSort (pown m arity) stateSort
            let constrTerms = List.init arity (fun _ -> Term.generateVariable s)
            let r = eqRec.IsFinal(Term.apply eqRec.Delta (constrTerms @ qTerms))
            let l =
                let constrEqs =
                    let eqOp = Operations.equal_op s
                    let t, ts = List.uncons constrTerms
                    List.map (fun el -> AApply(eqOp, [t; el])) ts
                let qDiag =
                    let qTerms = Array.ofList qTerms
                    let diagCoof = List.init arity (fun i -> pown m i) |> List.sum
                    List.init m (fun i -> qTerms.[i*diagCoof])
                constrEqs @ List.map eqRec.IsFinal qDiag
            clAEquivalence l r
        Automaton(eqRec, [initAxiom; deltaAxiom])

    member private x.GetOrAddEqualityAutomaton ts =
        let s = List.head ts |> Term.typeOf |> adtToConstrSort
        let n = List.length ts
        let baseAutomaton = Dictionary.getOrInitWith (s, n) equalities (fun () -> x.GenerateEqualityAutomaton s n)
        x.GetOrAddPatternAutomaton baseAutomaton (Pattern ts)

    member x.GetOrAddApplicationAutomaton op xs =
        let baseAutomaton = x.GetOrAddOperationAutomaton op
        x.GetOrAddPatternAutomaton baseAutomaton (Pattern xs)

    member x.TraverseDatatype (sName, xs) =
        let s = adtToConstrSort (ADTSort sName)
        let bot = x.getBotSymbol s
        let constructors = List.map (fst3 >> Operation.opName) xs
        let constrDecls = List.map (fun name -> DeclareConst(name, s)) constructors
        List.map FOLOriginalCommand (DeclareSort(sName) :: constrDecls)

    member private x.BottomizeTerms op ts =
        let s = adtToConstrSort (Operation.returnType op) //TODO: it works only for single sorted ADTs
        let bottom = x.getBottom s
        let ts' = List.map x.BottomizeTerm ts
        let ts'' = List.replicate (m - List.length ts') bottom
        ts' @ ts''
    member private x.BottomizeTerm = function
        | TApply(op, ts) ->
            let ts' = x.BottomizeTerms op ts
            TApply(op, ts')
        | t -> t

    member private x.IsBottom op =
        match Dictionary.tryFind (Operation.returnType op) botSymbols with
        | Some name -> Operation.opName op = name
        | None -> false

    member private x.deltaFromInitAxiom (aRecord: AutomatonRecord) sortList =
        let n = List.length sortList
        let inits = List.init (pown m n) (fun _ -> aRecord.Init)
        let botLists = List.map (adtToConstrSort >> x.getBottom) sortList
        let l = Term.apply aRecord.Delta (botLists @ inits)
        clAFact(Equal(l, aRecord.Init))


    member private x.GeneratePatternAutomaton strategy (baseAutomaton : Automaton) pattern =
        let linearizedPattern, equalVars = Pattern.linearizeVariables pattern
        let newVars = List.concat equalVars |> List.unique
        let instantiator = PatternAutomatonGenerator.linearInstantiator m linearizedPattern
        let A = AutomatonApply(baseAutomaton.Delta, linearizedPattern)
        let patternSorts = linearizedPattern |> Pattern.collectFreeVars |> SortedVars.sort
        let patternRec, B =
            let pattern' = patternSorts |> List.map TIdent |> Pattern
            let record = Automaton.fromPattern m strategy stateSort pattern'
            record, AutomatonApply(record.Delta, pattern')
        
        let strategyIsEmpty = PatternAutomatonGenerator.strategyIsEmpty x.IsBottom x.BottomizeTerms m strategy A
        if strategyIsEmpty then None
        else
        let A, B = PatternAutomatonGenerator.instantiate x.IsBottom x.BottomizeTerms strategy instantiator A B
        let finalStates, invariantA = PatternAutomatonGenerator.finalStatesAndInvariant A
        let leftSide, rightSide = PatternAutomatonGenerator.inductiveUnfoldings x.IsBottom x.BottomizeTerms strategy m B invariantA
        let delta = PatternAutomatonGenerator.inductionSchema leftSide rightSide
        let deltaFromInitAxiom = x.deltaFromInitAxiom patternRec (List.map snd patternSorts)
        let patAxioms = x.patternDeltaAndFinals baseAutomaton.Record patternRec delta finalStates
        if Option.isNone patAxioms then None
        else
            let patAxioms = Option.get patAxioms
            Some(Automaton(patternRec, deltaFromInitAxiom :: patAxioms))

    member private x.patternDeltaAndFinals (baseAutomaton : AutomatonRecord) (patternRec : AutomatonRecord) (deltaLeft, deltaRight) (finalConstrs, finalIdents, finalState) =
        let callsDiff = Invariant.difference deltaRight deltaLeft
        if not <| Set.isEmpty callsDiff then None
        else
        let constrsToTerms = List.map MetaConstructor.toTerm
        let rec constrStatesToTerm constrs states =
            x.Delay (constrsToTerms constrs) (List.map State_toTerm states) patternRec
        and State_toTerm = function
            | SInit -> baseAutomaton.Init
            | SVar name -> TIdent(name, stateSort)
            | DeltaApply(deltaOp, constrs, states) ->
                let terms = List.map State_toTerm states
                let constrs = constrsToTerms constrs
                Term.apply deltaOp (constrs @ terms)
            | CombinedState(constrs, states) -> constrStatesToTerm constrs states
            | AutomatonApply _ -> __unreachable__()
        let Invariant_toTerm (Invariant(constrs, states)) = constrStatesToTerm constrs states
        let initDecls =
            clAFact(Equal(patternRec.Init, baseAutomaton.Init))
        let deltaDecls =
            let r = Invariant_toTerm deltaRight
            let l =
                let t = State_toTerm deltaLeft
                match Term.tryCut t with
                | Some(_, ts) ->
                    if List.isEmpty ts then Term.apply patternRec.Delta [r] else Term.apply patternRec.Delta ts
                | None -> Term.apply patternRec.Delta [t]
            clAFact(Equal(l, r))
        let finalDecls = // """Fb(freeConstrs, abstrVars) <=> Fa(abstrState)"""
            let r = baseAutomaton.IsFinal(State_toTerm finalState)
            let finalTerms = List.map (fun name -> TIdent(name, stateSort)) finalIdents
            let l = patternRec.IsFinal(x.Delay (constrsToTerms finalConstrs) finalTerms patternRec)
            clAEquivalence [l] r
        let decls = initDecls :: deltaDecls :: finalDecls :: []
        Some(decls)

    member private x.GetOrAddPatternAutomaton baseAutomaton (Pattern pattern) =
        let vars = Terms.collectFreeVars pattern |> List.sortWith SortedVar.compare
        let renameMap = List.mapi (fun i (_, s as v) -> (v, TIdent ($"x_{i}", s))) vars |> Map.ofList
        let pattern = List.map (Term.substituteWith renameMap) pattern
        let maxArity = List.max [Terms.numVars pattern; Terms.length pattern]
        let strategyBuilder = StrategyBuilder(m, maxArity, false)
        let fcStrategy = strategyBuilder.Build()
        Dictionary.getOrInitWith (baseAutomaton, pattern) patternAutomata (fun () -> Option.get (x.GeneratePatternAutomaton fcStrategy baseAutomaton (Pattern pattern)))

    member private x.Delay constrs states patRec =
        assert(List.forall (fun t -> Term.typeOf t = stateSort) states)
        match constrs, states with
        | [], [] -> Term.generateVariable stateSort
        | [], [state] -> state
        | _ ->
        let constrsSorts = List.map Term.typeOf constrs
        let n = List.length states
        let generateDelayOperation () =
            let name = IdentGenerator.gensymp "delay"
            let op = Operation.makeElementaryOperationFromSorts name (constrsSorts @ List.replicate n stateSort) stateSort
            let axiom =
                let r = Term.apply op ((List.map (Term.typeOf >> x.getBottom) constrs) @ (List.map (fun _ -> patRec.Init) states))
                clAFact(equalStates patRec.Init r)
            op, axiom
        let op = fst (Dictionary.getOrInitWith patRec delays generateDelayOperation)
        Term.apply op (constrs @ states)

    member private x.Product terms =
        assert(List.forall (fun t -> Term.typeOf t = stateSort) terms)
        match terms with
        | [] -> Term.generateVariable stateSort
        | [t] -> t
        | _ ->
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
        | AApply(op, xs) -> Some(a, x.GetOrAddApplicationAutomaton op xs)
        | Distinct(y, z) -> __unreachable__()

    member private x.TraverseRule (rule.Rule(_, body, head)) =
        let pairHeadAndBody = List.cons
        let unpairHeadAndBody = List.uncons
        let headIsEmpty = Atom.collectFreeVars head = []
        let atoms, patAutomata = List.unzip <| List.choose x.GenerateAtomAutomaton (pairHeadAndBody head body)

        // process rule
        let atomsVars = atoms |> List.map Atom.collectFreeVars |> List.map SortedVars.sort |> List.filter (List.notEmpty)
                        |> List.map (List.map (fun (vname, vsort) -> (vname, adtToConstrSort vsort)))
        let emptyAutomata, patAutomata = patAutomata |> List.choose2 (fun a -> if Automaton.isEmpty a then Choice1Of2 a else Choice2Of2 a)

        let clauseName = IdentGenerator.gensymp "clause"
        let clauseVars = List.concat atomsVars |> List.unique |> SortedVars.sort
        let cRecord = Automaton.fromSorts m fcStrategy stateSort clauseName (List.map snd clauseVars)
        let clauseVarsTerms = clauseVars |> List.map TIdent

        let initAxiom =
            let l = cRecord.Init
            let inits = patAutomata |> List.map (fun (r : Automaton) -> r.Init)
            let r = x.Product inits
            clAFact (equalStates l r)
        let deltaAxioms =
            let deltaFromInitAxiom = x.deltaFromInitAxiom cRecord (List.map snd clauseVars)
            let stateTerms = List.map (fun vars -> (Terms.generateNVariablesOfSort (pown m (List.length vars)) stateSort)) atomsVars
            let atomsTerms = List.map (List.map TIdent) atomsVars
            let rs = List.map3 (fun (r : Automaton) vs s -> Term.apply r.Delta (vs @ s)) patAutomata atomsTerms stateTerms
            let r = x.Product rs
            let l =
                // helper functions
                let genQMask aVars = List.map (fun v -> List.contains v aVars) clauseVars
                let applyMask combination mask =
                    List.zip combination mask
                 |> List.filter snd
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
                Term.apply cRecord.Delta (clauseVarsTerms @ lStates)
            [deltaFromInitAxiom; clAFact (equalStates l r)]
        let finalAxiom =
            let stateTerms = Terms.generateNVariablesOfSort (List.length patAutomata) stateSort
            let li = x.Product stateTerms
            let l = FOLAtom <| cRecord.IsFinal li
            let rs =
                let empties = List.map (fun (r : Automaton) -> FOLAtom(r.IsFinal(Term.generateVariable stateSort))) emptyAutomata
                let nonEmpties = List.map2 (fun (r : Automaton) -> r.IsFinal >> FOLAtom) patAutomata stateTerms
                if headIsEmpty then empties @ nonEmpties else nonEmpties @ empties
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
            let r = cRecord.Reach(Term.apply cRecord.Delta (clauseVarsTerms @ qTerms))
            clARule l r
        let condition = // negation of the clause: each reachable is not final
            let qTerm = Term.generateVariable stateSort
            clARule [cRecord.Reach qTerm; cRecord.IsFinal qTerm] Bot
        let tCommands =
            let common = [finalAxiom; reachInit; reachDelta; condition]
            if List.isEmpty clauseVars then common else initAxiom :: deltaAxioms @ common

        cRecord.Declarations @ tCommands

    member private x.GetOrAddOperationAutomaton op =
        Dictionary.getOrInitWith op applications (fun () -> Automaton(Automaton.fromOperation m fcStrategy stateSort op, []))

    member private x.GenerateBotDeclarations () =
        botSymbols |> Dictionary.toList |> List.map (fun (s, n) -> FOLOriginalCommand(DeclareFun(n, [], s)))
    member private x.GenerateFunDeclarations () =
        applications |> Dictionary.toList |> List.collect (fun (_, aut)-> aut.Declarations)
    member private x.GenerateProductDeclarations () = dumpOpDictionary products
    member private x.GenerateDelayDeclarations () =
        delays |> Dictionary.toList |> List.collect (fun (_, (op, axiom)) -> [FOLOriginalCommand(Command.declareOp op); axiom])        

    member private x.GeneratePatternDeclarations () =
        patternAutomata |> Dictionary.toList |> List.collect (fun (_, a) -> a.Declarations)

    member private x.GenerateEqDeclarations () =
        equalities |> Dictionary.toList |> List.collect (fun (_, a) -> a.Declarations)

    member private x.TraverseCommand = function
        | DeclareFun(_, _, BoolSort) -> []
        | DeclareDatatype dt -> x.TraverseDatatype dt
        | DeclareDatatypes dts -> List.collect x.TraverseDatatype dts
        | c -> [FOLOriginalCommand c]

    member private x.TraverseTransformedCommand = function
        | OriginalCommand o -> x.TraverseCommand o
        | TransformedCommand rule -> rule |> Rule.linearize |> x.TraverseRule
//        | TransformedCommand rule -> rule |> Rule.normalize |> Rule.linearize |> x.TraverseRule
        | LemmaCommand _ -> __unreachable__()

    member private x.collectPatterns command =
        let helper a =
            match a with
            | Top | Bot -> None
            | Equal (t1, t2) ->
                let eqOp = Operations.equal_op (Term.typeOf t1)
                Some(eqOp, Pattern([t1; t2]))
            | AApply(op, ts) ->
                Some(op, Pattern(ts))
            | Distinct _ -> __unreachable__()
        match command with
        | OriginalCommand _ -> []
        | TransformedCommand rule -> rule |> Rule.linearize |> Rule.fold (fun s a -> (helper a)::s) List.empty
        | LemmaCommand _ -> __unreachable__()
            
    member private x.GetStrategy aloud op linearPatterns =
        // TODO: should we linearize here?
        let maxVars =
            let patVars = linearPatterns |> List.map Pattern.numVars
            let patLengths = linearPatterns |> List.map Pattern.length
            List.max (patVars @ patLengths) 
        let strategyBuilder = StrategyBuilder(m, maxVars, aloud)
        let baseAut = Automaton(Automaton.fromOperation m fcStrategy stateSort op, [])
        
        let mutable ok = true
        while ok do
            let strategy = strategyBuilder.Build()
            let res = List.map (x.GeneratePatternAutomaton strategy baseAut) linearPatterns
            if List.exists Option.isNone res then
                strategyBuilder.BacktrackStrategy()
                if aloud then printfn ": stays"
            if strategyBuilder.IsReducible() then
                if aloud then printfn ""
                strategyBuilder.ImproveCurrentStrategy()
            else
                ok <- false
        strategyBuilder.Build()

    member x.GeneratePatternAutomata aloud op patterns =
        let patterns, eqVars = List.unzip <| List.map Pattern.linearizeVariables patterns
        let strategy = x.GetStrategy aloud op patterns
        let opAutomaton = Automaton(Automaton.fromOperation m strategy stateSort op, [])
        let patAutomata = List.map (x.GeneratePatternAutomaton strategy opAutomaton) patterns
        // TODO: process equalities
        patAutomata
    
    member x.TraverseCommands commands =
        let header = List.map (DeclareSort >> FOLOriginalCommand) [stateSortName; adtConstructorSortName]
//        let pats = commands |> List.collect x.collectPatterns
//                            |> List.unique
//                            |> List.choose id
//                            |> List.groupBy fst
//                            |> List.map x.GeneratePatternAutomatons
        let commands' = List.collect x.TraverseTransformedCommand commands
        let botDecls = x.GenerateBotDeclarations ()
        let funDecls = x.GenerateFunDeclarations ()
        let prodDecls = x.GenerateProductDeclarations ()
        let delayDecls = x.GenerateDelayDeclarations ()
        let patDecls = x.GeneratePatternDeclarations ()
        let eqDecls = x.GenerateEqDeclarations ()
        let all = header @ botDecls @ funDecls @ eqDecls @ patDecls @ prodDecls @ delayDecls @ commands'
        let sortDecls, rest = List.choose2 (function FOLOriginalCommand(DeclareSort _) as s -> Choice1Of2 s | c -> Choice2Of2 c) all
        let funDecls, rest = List.choose2 (function FOLOriginalCommand(DeclareFun _ | DeclareConst _) as s -> Choice1Of2 s | c -> Choice2Of2 c) rest
        sortDecls @ funDecls @ rest

let transform (commands : list<transformedCommand>) =
    let maxConstructorWidth = List.max <| List.map (function OriginalCommand c -> Command.maxConstructorArity c | _ -> Datatype.noConstructorArity) commands
    let processer = ToTTATraverser(maxConstructorWidth)
    processer.TraverseCommands(commands)
