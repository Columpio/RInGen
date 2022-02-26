module RInGen.TtaTransform

open System.Collections.Generic
open FOLCommand
open Operations

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

    override r.ToString() = r.Name

type private state =
    | SVar of ident
    | CombinedState of operation list * state list // ``Delay'' states
    | AutomatonApply of ident * pattern
    | DeltaApply of ident * operation list * state list
    override x.ToString() =
        match x with
        | SVar i -> i
        | AutomatonApply(name, pat) -> $"%s{name}[{pat}]"
        | CombinedState(constrs, states) ->
            let cs = constrs |> List.map toString |> join ", "
            let ss = states |> List.map toString |> join ", "
            $"""((%s{cs}), (%s{ss}))"""
        | DeltaApply(name, constrs, states) ->
            let cs = constrs |> List.map toString |> join ", "
            let ss = states |> List.map toString |> join ", "
            $"""delta%s{name}(%s{cs}, %s{ss})"""

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

    let extractFromRule (Rule(_, body, head)) = List.choose extractFromAtom (head::body)

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

    let private isMetaVariableForConstructor _ = __notImplemented__()

    let freeConstructors =
        let rec freeConstructors free state =
            match state with
            | DeltaApply(_, constrs, states) ->
                List.fold freeConstructors (constrs |> List.filter isMetaVariableForConstructor |> Set.ofList |> Set.union free) states
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

    let abstractAutomatonApplies =
        let helper ((vars2states, states2vars) as maps) name pat =
            let a = AutomatonApply(name, pat)
            match Map.tryFind a states2vars with
            | Some ident -> SVar ident, maps
            | None ->
                let freshName = IdentGenerator.gensym ()
                SVar freshName, (Map.add freshName a vars2states, Map.add a freshName states2vars)
        mapFoldAutomatonApplies helper (Map.empty, Map.empty)

    let collectAutomatonApplies = foldAutomatonApplies (fun states name pat -> Set.add (AutomatonApply(name, pat)) states) Set.empty

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

    let collectAutomatonApplies (Invariant(_, states)) = states |> List.map State.collectAutomatonApplies |> Set.unionMany

module private PatternAutomatonGenerator =
    let linearInstantiator width pattern =
        let var2depth = Pattern.collectVariableDepths pattern
        let patDepth = Pattern.depth pattern
        var2depth |> Map.map (fun _ depth -> Term.falsehood) //TODO: Term.mkFullTree width (patDepth - depth))

    let instantiate instantiator A B =
        let A' = State.instantiate instantiator A
        let B' = State.instantiate instantiator B
        let A'' = State.unfoldAutomatonApplyRec A'
        A'', B'

    let finalStatesAndInvariant A B =
        // returns $"""Fb := {{ (({freeConstrsStr}), ({abstrVars |> List.map toString |> join ", "})) |{"\n\t"}{abstrState} \in Fa }}"""
        let abstrState, (abstrVarsMap, _) = State.abstractAutomatonApplies A
        let abstrVars = abstrVarsMap |> Map.toList |> List.map fst
        let freeConstrs = State.freeConstructors abstrState
        let inv = Invariant.fromConstructorsAndStates freeConstrs (List.map (Map.findOrApply SVar abstrVarsMap) abstrVars)
        (freeConstrs, abstrVars, abstrState), inv

    let inductiveUnfoldings width B invariantA =
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
                match Map.tryFind a state2vars with
                | Some ident -> SVar ident
                | None -> a
            Invariant.mapAutomatonApplies mapper rightSide
        abstrLeftSide, abstrRightSide

    let pattern2a pattern = AutomatonApply("A", pattern)
    let pattern2b pattern =
        let pattern' = pattern |> Pattern.collectFreeVars |> List.map TIdent                                                 // each variable one time
    //    let pattern' = pattern |> Pattern.freeVarsMap |> Map.toList |> List.collect (fun (v, n) -> List.init n (fun _ -> Var v)) // each variable n times
        AutomatonApply("B", Pattern pattern')

    let private automatonFromDeltaAndFinals delta finalStates =
        __notImplemented__()

    let generatePatternAutomaton width pattern =
        let generalizedPattern, vars2vars = Pattern.generalizeVariables pattern
        let newVars = Map.toList vars2vars |> List.map fst |> List.unique
        let instantiator = linearInstantiator width generalizedPattern
        let A = pattern2a generalizedPattern
        let B = pattern2b generalizedPattern
        let A, B = instantiate instantiator A B
        let finalStates, invariantA = finalStatesAndInvariant A B
        let leftSide, rightSide = inductiveUnfoldings width B invariantA
        let delta = inductionSchema leftSide rightSide
        let patAutomaton = automatonFromDeltaAndFinals delta finalStates
//        let equalityAutomaton = buildEqualityAutomaton newVars
//        let intersectionAutomaton = intersect equalityAutomaton patAutomaton
//        let prAutomaton = proj newVars intersectionAutomaton //TODO: do we really need it?
//        intersectionAutomaton
        patAutomaton

module private Automaton =
    let fromSorts m stateSort name sortList =
        let initStateName = "init_" + name
        let isFinalName = "isFinal_" + name
        let deltaName = "delta_" + name
        let reachName = "reach_" + name
        let statesVec =
            let n = List.length sortList
            List.replicate (pown m n) stateSort

        let initState = Operation.makeElementaryOperationFromSorts initStateName [] stateSort
        let isFinal = Operation.makeElementaryRelationFromSorts isFinalName [stateSort]
        let delta = Operation.makeElementaryOperationFromSorts deltaName (sortList @ statesVec) stateSort
        let reach = Operation.makeElementaryRelationFromSorts reachName [stateSort]
        AutomatonRecord(name, initState, isFinal, delta, reach)

    let fromPattern m stateSort (Pattern terms) =
        let vars = Terms.collectFreeVars terms |> List.sortWith SortedVar.compare
//        let renameMap = Terms.generateVariablesFromVars vars |> List.zip vars |> Map.ofList
//        let renamedTerms = List.map (Term.substituteWith renameMap) terms
        let sorts = vars |> List.map snd
        let name = IdentGenerator.gensymp "pat"
        fromSorts m stateSort name sorts

type private ToTTATraverser(m : int) =
    let stateSortName = IdentGenerator.gensymp "State"
    let stateSort = FreeSort stateSortName

    let equal s = Atom.apply2 (equal_op s)
    let equalStates = equal stateSort

    let botSymbols = Dictionary<_, _>()
    let patternAutomata = Dictionary<_, _>()
    let equalities = Dictionary<_, _>()

    member private x.getBotSymbol sort =
        Dictionary.getOrInitWith sort botSymbols (fun () -> IdentGenerator.gensymp <| Sort.sortToFlatString sort + "_bot")

    member private x.getEqRelName s arity =
        Dictionary.getOrInitWith (s, arity) equalities (fun () -> IdentGenerator.gensymp $"eq_{s}_{arity}")

    member private x.getDiseqRelName s = // TODO: no need after diseq transform
        "diseq" + s.ToString()

    member private x.GenerateAutomaton name args = Automaton.fromSorts m stateSort name args

    member private x.GenerateEqualityAutomaton s arity =
        let eqRelName = x.getEqRelName s arity
        let eqRec = x.GenerateAutomaton eqRelName (List.replicate arity s)

        let initAxiom = clAFact(eqRec.IsFinal eqRec.Init)
        let deltaAxiom =
            let qTerms = Terms.generateNVariablesOfSort (pown m arity) stateSort
            let constrTerms = List.init arity (fun _ -> Term.generateVariable s)
            let l = eqRec.IsFinal(eqRec.Delta(constrTerms @ qTerms))
            let r =
                let constrEqs =
                    let eqOp = equal_op s
                    let t, ts = List.uncons constrTerms
                    List.map (fun el -> AApply(eqOp, [t; el])) ts
                let qDiag =
                    let qTerms = Array.ofList qTerms
                    let diagCoof = List.init arity (fun i -> pown m i) |> List.sum
                    List.init m (fun i -> qTerms.[i*diagCoof])
                constrEqs @ List.map eqRec.IsFinal qDiag
            clAEquivalence r l
        eqRec.Declarations @ [initAxiom; deltaAxiom]

    member private x.TraverseDatatype (sName, xs) =
        let s = ADTSort sName
        let constructors = x.getBotSymbol s :: List.map (fst3 >> Operation.opName) xs
        let constrDecls = List.map (fun name -> DeclareConst(name, s)) constructors
        List.map FOLOriginalCommand (DeclareSort(sName) :: constrDecls)

    member private x.GetOrAddPattern (Pattern pattern) =
        let vars = Terms.collectFreeVars pattern |> List.unique |> List.sortWith SortedVar.compare
        let renameMap = List.mapi (fun i v -> (v, TIdent ("x_" + i.ToString(), snd v))) vars |> Map.ofList
        let pattern = List.map (Term.substituteWith renameMap) pattern
        Dictionary.getOrInitWith pattern patternAutomata (fun () ->
            Automaton.fromPattern m stateSort (Pattern pattern))
//            PatternAutomatonGenerator.generatePatternAutomaton m (Pattern pattern))

    member private x.TraverseRule (Rule(_, body, head) as rule) =
        let atoms = head :: body
        let atoms = List.filter (function | Top | Bot -> false | _ -> true) atoms
        let patAutomata = Pattern.extractFromRule rule |> List.map x.GetOrAddPattern

        let clauseName = IdentGenerator.gensymp "clause"
        let clauseVars = Atoms.collectFreeVars atoms |> List.sortWith SortedVar.compare
        let cRecord = x.GenerateAutomaton clauseName (List.map snd clauseVars)

        // process rule
        let atomsVars = atoms |> List.map Atom.collectFreeVars |> List.map (List.sortWith SortedVar.compare)
        let clauseVarsTerms = clauseVars |> List.map TIdent

        let clauseLen = atomsVars |> List.length

        let prodOp =
            let prodName = "prod_" + clauseName
            let ss = List.replicate clauseLen stateSort
            Operation.makeElementaryOperationFromSorts prodName ss stateSort

        let initAxiom =
            let l = cRecord.Init
            let inits = patAutomata |> List.map (fun (r : AutomatonRecord) -> r.Init)
            let r = TApply(prodOp, inits)
            clAFact (equalStates l r)
        let deltaAxiom =
            let stateTerms = List.map (fun vars -> (Terms.generateNVariablesOfSort (pown m (List.length vars)) stateSort)) atomsVars
            let atomsTerms = List.map (List.map TIdent) atomsVars
            let rs = List.map3 (fun (r : AutomatonRecord) vs s -> r.Delta(vs @ s)) patAutomata atomsTerms stateTerms
            let r = TApply(prodOp, rs)
            let l =
                // helper functions
                let genQMask aVars = List.map (fun v -> List.contains v aVars) clauseVars
                let applyMask combination mask =
                    List.zip combination mask |> List.filter snd |> List.rev |>
                    List.mapi (fun i (el,_) -> el * (pown m i)) |> List.sum

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
                let lStates = List.map (fun qs -> TApply(prodOp, qs)) stateTerms
                cRecord.Delta(clauseVarsTerms @ lStates)
            clAFact (equalStates l r)
        let finalAxiom =
            let stateTerms = Terms.generateNVariablesOfSort clauseLen stateSort
            let li = TApply(prodOp, stateTerms)
            let l = FOLAtom <| cRecord.IsFinal li
            let rs, lastR = List.butLast patAutomata
            let states, lastStates = List.butLast stateTerms
            let rs = List.map2 (fun (r : AutomatonRecord) -> FOLAtom << r.IsFinal) rs states
            // head isFinal is negated
            let lastR = FOLAtom <| lastR.IsFinal lastStates
            let lastR =
                match head with
                | Bot -> lastR
                | _ -> FOLNot lastR
            clAEquivalenceFromFOL (lastR :: rs) l
        let reachInit =
            clAFact (cRecord.Reach cRecord.Init)
        let reachDelta =
            let qTerms = Terms.generateNVariablesOfSort (pown m (List.length clauseVarsTerms)) stateSort
            let l = List.map cRecord.Reach qTerms
            let r = cRecord.Reach(cRecord.Delta(clauseVarsTerms @ qTerms))
            clARule l r
        let condition =
            let qTerm = Term.generateVariableWithPrefix("q", stateSort)
            clARule [cRecord.Reach qTerm; cRecord.IsFinal qTerm] Bot
        let tCommands = [initAxiom; deltaAxiom; finalAxiom; reachInit; reachDelta; condition]

        let clauseDecls =
            let prodDecl = FOLOriginalCommand <| Command.declareOp prodOp
            prodDecl :: cRecord.Declarations

        clauseDecls @ tCommands

    member private x.TraverseCommand = function
        | DeclareFun(fname, args, BoolSort) -> (x.GenerateAutomaton fname args).Declarations
        | DeclareDatatype dt -> x.TraverseDatatype dt
        | DeclareDatatypes dts -> List.collect x.TraverseDatatype dts
        | c -> [FOLOriginalCommand c]

    member private x.traversePatterns =
        let res = seq {
            for KeyValue(_, aRec) in patternAutomata do
                yield! aRec.Declarations
        }
        List.ofSeq res

    member x.TraverseCommands commands =
        let commands, rules = List.choose2 (function OriginalCommand o -> Choice1Of2 o | TransformedCommand t -> Choice2Of2 t | LemmaCommand _ -> __unreachable__()) commands
        let commands' = List.collect x.TraverseCommand commands
        let rules' = List.collect x.TraverseRule rules
        let header = FOLOriginalCommand(DeclareSort(stateSortName))
        let patternsAxioms = x.traversePatterns
        header :: commands' @ patternsAxioms @ rules'

let transform (commands : transformedCommand list) =
    let maxConstructorWidth = List.max <| List.map (function OriginalCommand c -> Command.maxConstructorArity c | _ -> Datatype.noConstructorArity) commands
    let processer = ToTTATraverser(maxConstructorWidth)
    processer.TraverseCommands(commands)
