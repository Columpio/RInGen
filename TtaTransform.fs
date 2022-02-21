module RInGen.TtaTransform

open System.Collections.Generic
open Microsoft.FSharp.Collections
open RInGen
open RInGen.IdentGenerator

let stateSort = gensymp "State" |> PrimitiveSort
let notop = Operation.makeElementaryRelationFromSorts "not" [boolSort]

let ordSort (s1 : sort) (s2 : sort) =
    let getSortName sv =
        match sv with
        | PrimitiveSort(name)
        | CompoundSort(name, _) -> name
    let s1 = getSortName s1
    let s2 = getSortName s2
    if s1 < s2 then -1 else
    if s1 > s2 then 1 else
    0

let ordSortedVar (sv1 : sorted_var) (sv2 : sorted_var) =
    let sort1 = snd sv1
    let sort2 = snd sv2
    let cmpSorts = ordSort sort1 sort2
    // prioritize sort name in comparison
    if cmpSorts <> 0 then cmpSorts else
    if fst sv1 < fst sv2 then -1 else
    if fst sv1 > fst sv2 then 1 else
    0

type namedPattern = Pattern of string * term list
type AutomataRecord =
    { name : ident
      initConst : term
      isFinal : operation
      delta : operation
      reach: operation }
type pattern =
    { baseAutomata : AutomataRecord
      terms : term list }

    member x.getVars() =
        collectFreeVarsInTerms x.terms |> Set.ofList

let rec renameVars fromToMap term =
    match term with
    | TIdent(name, sort) ->
        let newName = Map.find name fromToMap
        TIdent(newName, sort)
    | TConst(_) -> term
    | TApply(op, ts) ->
        let renamedTerms = List.map (renameVars fromToMap) ts
        TApply(op, renamedTerms)

type Processer(adts) =
    // TODO: optimization
    let m = adts |> List.map snd |> List.concat |> List.map snd |> List.map (List.length) |> List.max
    member private x.getEqRelName s =
        "eq" + s.ToString()
    member private x.getDiseqRelName s =
        "diseq" + s.ToString()

    member x.extractPattern atom =
        let name, terms =
            match atom with
            | Top | Bot -> None, []
            | Distinct(t1, t2) ->
                let sort = t1.getSort()
                Some (x.getDiseqRelName sort), [t1; t2]
            | Equal(t1, t2) ->
                let sort = t1.getSort()
                Some (x.getEqRelName sort), [t1; t2]
            | AApply(op, ts) -> Some (op.ToString()), ts
        if Option.isNone name then None
        else
        let vars = collectFreeVarsInTerms terms |> Set.ofList
        let renameMap = Seq.mapi (fun i v -> (fst v, "x_" + i.ToString())) vars |> Map.ofSeq
        let renamedTerms = List.map (renameVars renameMap) terms
        let _, baseAutomata =
            let sorts = terms |> List.map (fun (t : term) -> t.getSort())
            x.generateAutomataDeclarations (Option.get name) sorts
        Some ({baseAutomata = baseAutomata; terms=renamedTerms})

    member x.generateAutomataDeclarations name sortList =
        let initStateName = "init_" + name
        let isFinalName = "isFinal_" + name
        let deltaName = "delta_" + name
        let reachName = "reach_" + name
        let statesVec =
            let n = List.length sortList
            List.init (pown m n) (fun _ -> stateSort)

        let decls =
            let initStateDecl = DeclareConst (initStateName, stateSort)
            let isFinalDecl = DeclareFun(isFinalName, [stateSort], boolSort)
            let deltaDecl = DeclareFun(deltaName, sortList @ statesVec, stateSort)
            let reachDecl = DeclareFun(reachName, [stateSort], boolSort)
            [initStateDecl; isFinalDecl; deltaDecl; reachDecl]

        let aRec =
            let initState = TConst(initStateName, stateSort)
            let isFinal = Operation.makeElementaryRelationFromSorts isFinalName [stateSort]
            let delta = Operation.makeElementaryOperationFromSorts deltaName (sortList @ statesVec) stateSort
            let reach = Operation.makeElementaryRelationFromSorts reachName [stateSort]
            {name=name; initConst = initState; isFinal = isFinal; delta = delta; reach=reach}

        List.map OriginalCommand decls, aRec

    member x.processDeclarations oCommands =
        let getDecls el =
            match el with
            | DeclareFun(fname, args, _) ->
                let decls, _ = x.generateAutomataDeclarations fname args
                Some decls
            | _ -> None

        let xs = oCommands |> List.map getDecls |> List.filter (fun el -> el.IsSome)

        seq {
            for el in xs do
                match el with
                | Some c -> yield! c
                | None -> ()
        }

    member x.parseDatatypes adts =
        let processDt(s, xs) =
            let constructors = List.map (fun x -> DeclareConst (fst x, s)) xs
            let bot = DeclareConst(s.getBotSymbol(), s)
            let baseDecls =
                 List.map OriginalCommand ([DeclareSort(s); bot] @ constructors)
            // eq axioms
            let automataDecls, eqRec =
                let eqRelName = x.getEqRelName s
                x.generateAutomataDeclarations eqRelName [s; s]

            let initAxiom =
                let r = AApply(eqRec.isFinal, [eqRec.initConst])
                TransformedCommand (rule [] [] r)
            let deltaAxiom =
                let qVars = List.init (pown m 2) (fun _ -> (gensym(), stateSort))
                let qTerms = List.map TIdent qVars
                let fVar, gVar = ("f", s), ("g", s)
                let fTerm, gTerm = TIdent fVar, TIdent gVar
                let l = AApply(eqRec.isFinal, [TApply(eqRec.delta, [fTerm; gTerm] @ qTerms)])
                let r =
                    let rl = AApply(equal_op s, [fTerm; gTerm])
                    let qDiag = List.init m (fun i -> qTerms.[i*(m+1)])
                    let rr = List.map (fun v -> AApply(eqRec.isFinal, [v])) qDiag
                    [rl] @ rr
                let rule = eqRule ([fVar; gVar] @ qVars) r l
                TransformedCommand rule

            // TODO: diseq + diseqAxioms ??
            // Note : diseq decls are generated twice, see parseDeclarations
            baseDecls @ automataDecls @ [initAxiom; deltaAxiom]

        seq {
            for c in adts do
                yield! (processDt c)
        }

    member private x.CollectFreeVarsInAtom = function
       | AApply(_, ts) -> collectFreeVarsInTerms ts
       | Equal(t1, t2) | Distinct(t1, t2) -> collectFreeVarsInTerms [t1; t2]
       | Bot | Top -> []
    member private x.CollectFreeVarsInAtoms = List.collect x.CollectFreeVarsInAtom

    member x.procRule clauseNum r patAutomata =
        let body, head =
            match r with
            | Rule(_,body, head) -> body, head
            | _ -> __unreachable__()

        let atoms = body @ [head] |> List.filter (function |Top | Bot -> false |_ -> true)

        // process rule
        let clauseName = "clause" + clauseNum.ToString()
        let atomsVars = atoms |> List.map x.CollectFreeVarsInAtom |> List.map (List.sortWith ordSortedVar)
        let clauseVars = x.CollectFreeVarsInAtoms atoms |> Set.ofList |> Set.toList |> List.sortWith ordSortedVar
        let clauseVarsTerms = clauseVars |> List.map TIdent
        let clauseSorts = clauseVars |> List.map snd
        let clauseDecls, cRecord = x.generateAutomataDeclarations clauseName clauseSorts

        let clauseLen = List.length patAutomata
        let prodName = "prod_" + clauseName

        let prodDecl, prodOp =
            let ss = List.init clauseLen (fun _ -> stateSort)
            let op = Operation.makeElementaryOperationFromSorts prodName ss stateSort
            let decl = OriginalCommand (DeclareFun(prodName, ss, stateSort))
            decl, op
        let clauseDecls = prodDecl::clauseDecls

        let initAxiom =
            let l = cRecord.initConst
            let inits = List.map (fun r -> r.initConst) patAutomata
            let r = TApply(prodOp, inits)
            rule [] [] (AApply(equal_op stateSort, [l; r]))
        let deltaAxiom =
            let stateVars = List.map (fun vars -> (List.init (pown m (List.length vars)) (fun _ -> (gensym(), stateSort)))) atomsVars
            let stateTerms = stateVars |> List.map (List.map TIdent)
            let atomsTerms = List.map (List.map TIdent) atomsVars
            let rs = List.map3 (fun r vs s -> TApply(r.delta, vs @ s) ) patAutomata atomsTerms stateTerms
            let r = TApply(prodOp, rs)
            let l =
                // helper functions
                let genQMask aVars = [
                        for v in clauseVars do
                            if (List.contains v aVars) then
                                yield true
                            else
                                yield false
                    ]
                let applyMask combination mask =
                    List.zip combination mask |> List.filter snd |> List.rev
                    |> List.mapi (fun i (el,_) -> el * (pown m i)) |> List.sum

                (*
                    masks ~ used ADT variables in atom
                    example: if clauseVars= [f1; f2; f3], atomVars=[f1;f3] then mask=[T; F; T]
                *)
                let posMasks = List.map genQMask atomsVars
                let combinations =
                    let rec f n m acc =
                        match n with
                        | 0 -> List.rev acc
                        | _ ->
                            let helper = f (n-1) m
                            let iList = (List.init m (fun i -> i::acc))
                            iList |> List.map helper |> List.concat
                    let allNumbersBaseM n m = List.chunkBySize n (f n m [])
                    // if n = 0 then [] else
                    allNumbersBaseM (List.length clauseVars) m
                (*
                    generate from [q0*; q1*] (n=1) -> [q0*; q0*; q1*; q1*] which can be used in prod
                    with [q00; q01; q10; q11] (n=2)
                *)
                let statePositions = List.map (fun c -> List.map (applyMask c) posMasks) combinations
                let stateTerms = statePositions |> List.map (fun positions -> List.map2 (List.item) positions stateTerms)
                let lStates = List.map (fun qs -> TApply(prodOp, qs)) stateTerms
                TApply(cRecord.delta, clauseVarsTerms @ lStates)
            rule (List.concat stateVars @ clauseVars) [] (AApply(equal_op stateSort, [l; r]))
        let finalAxiom =
            let stateVars = List.init clauseLen (fun _ -> (gensym(), stateSort))
            let stateTerms = stateVars |> List.map TIdent
            let li = TApply(prodOp, stateTerms)
            let l = AApply(cRecord.isFinal, [li])
            let rs,lastR = patAutomata |> List.splitAt (clauseLen - 1)
            let states, lastStates = stateTerms |> List.splitAt (clauseLen - 1)
            let rs = List.map2 (fun r q -> AApply(r.isFinal, [q]) ) rs states
            // head isFinal is negated
            let lastR = List.exactlyOne lastR
            let lastR =
                match head with
                | Bot ->
                    AApply(lastR.isFinal, lastStates)
                | _ ->
                    AApply(notop, [TApply(lastR.isFinal, lastStates)])
            eqRule stateVars (rs @ [lastR]) l
        let reachInit =
            rule [] [] (AApply(cRecord.reach, [cRecord.initConst]))
        let reachDelta =
            let qVars = List.init (pown m (List.length clauseVarsTerms)) (fun _ -> (gensym(), stateSort))
            let qTerms = List.map TIdent qVars
            let l = List.map (fun q -> AApply(cRecord.reach, [q])) qTerms
            let r =
                let ri = TApply(cRecord.delta, clauseVarsTerms @ qTerms)
                AApply(cRecord.reach, [ri])
            rule (clauseVars @ qVars) l r
        let condition =
            let qVar = ("q", stateSort)
            let qTerm = TIdent qVar
            let l = AApply(cRecord.reach, [qTerm])
            let r = AApply(notop, [TApply(cRecord.isFinal, [qTerm])])
            rule [qVar] [l] r
        let tCommands = [initAxiom; deltaAxiom; finalAxiom; reachInit; reachDelta; condition]

        clauseDecls @ List.map TransformedCommand tCommands

    member x.ruleToPatterns = function
        | Rule(_, body, head) ->
            List.map x.extractPattern (body @ [head]) |>
                List.filter (Option.isSome) |> List.map (Option.get)

    member x.generatePatternAxioms (p:namedPattern) (patRec:AutomataRecord) (baseRec:AutomataRecord) =
        // not implemented
        // will return list of rules
        // TODO: have to pass m as param
        []

    member x.procRules rules =
//        let querries, rules = List.choose2 (function | Rule(_,_,head) as r -> match head with | Bot -> Choice1Of2 r | _ -> Choice2Of2 r) rules
        let patternedRules = List.map x.ruleToPatterns rules

        let patternSet = patternedRules |> List.concat |> Set.ofList
        let patternVars = patternSet |> Seq.map (fun p -> p.getVars())
        let decls, patternToRecordMap =
            let f i pat vars =
                let name = "P" + i.ToString()
                let sorts = vars |> Seq.map snd |> List.ofSeq |> List.sortWith ordSort
                let decls, record = x.generateAutomataDeclarations name sorts
                (decls, (pat, record))
            let decls, patternToRecordMap = Seq.mapi2 f patternSet patternVars |> List.ofSeq |> List.unzip
            List.concat decls, Map.ofList patternToRecordMap
        let patternAxioms = seq {
            for KeyValue(pat, patRec) in patternToRecordMap do
                let namedPattern = Pattern(patRec.name, pat.terms)
                yield! (x.generatePatternAxioms namedPattern patRec pat.baseAutomata)
        }
        let patternAxioms = patternAxioms |> Seq.toList
        let automataRules = patternedRules |> List.map (List.map (fun p -> Map.find p patternToRecordMap))

        decls @ patternAxioms @ (List.mapi2 x.procRule rules automataRules |> List.concat)

    member x.traverseCommands oCommands (rules : rule list)  =
        seq {
            yield OriginalCommand(DeclareSort(stateSort))
            yield! (x.parseDatatypes adts)
            yield! (x.processDeclarations oCommands)
            // TODO: remove ltlt debug
            // How to handle patterns with no variables?
            yield! (x.procRules [rules.[6]; rules.[7]; rules.[8]])
        }

let transform commands =
    let commandParser = function
        | OriginalCommand o -> Choice1Of2 o
        | TransformedCommand t -> Choice2Of2 t
        | _ -> __unreachable__()
    let oCommands, tComands = List.choose2 commandParser commands
    let adt_decls, oCommands = oCommands |> List.choose2 (function DeclareDatatype(a, b) -> Choice1Of2 [(a, b)] | DeclareDatatypes dts -> Choice1Of2 dts | c -> Choice2Of2 c)
    let adt_decls = List.concat adt_decls
    let processer = Processer(adt_decls)
    let commands = processer.traverseCommands oCommands tComands
    let commands = commands |> Seq.toList
    commands
