module RInGen.TtaTransform

open System.Collections.Generic
open Microsoft.FSharp.Collections
open RInGen
open RInGen.IdentGenerator

let stateSort = gensymp "State" |> PrimitiveSort
let notop = Operation.makeElementaryRelationFromSorts "not" [boolSort]

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
            let sorts = terms |> List.map (fun (t : term) -> t.getSort()) |> List.sort
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

    member x.procAtom clauseNum posNum atom =
        let posName = "pos_C" + clauseNum.ToString() + "_" + posNum.ToString()
        let baseName, baseSortList, posVarList =
            match atom with
            | Bot | Top -> "", [], []
            | Equal(t1, t2) ->
                let s = t1.getSort()
                x.getEqRelName s, [s; s], collectFreeVarsInTerms [t1; t2]
            | Distinct(t1, t2) ->
                let s = t1.getSort()
                x.getDiseqRelName s, [s; s], collectFreeVarsInTerms [t1; t2]
            | AApply(op, ts) -> op.ToString(), List.map (fun (t: term) -> t.getSort()) ts, collectFreeVarsInTerms ts

        if List.isEmpty baseSortList then None else

        let posSortList = List.map snd posVarList
        let posDecls, posRecord = x.generateAutomataDeclarations posName posSortList
        let _, baseRecord = x.generateAutomataDeclarations baseName baseSortList
        let initAxiom = AApply(equal_op stateSort, [posRecord.initConst; baseRecord.initConst])
        let initAxiom = rule [] [] initAxiom
        Some(posRecord, posDecls @ [TransformedCommand initAxiom])

    member x.procRule clauseNum r =
        let body, head =
            match r with
            | Rule(_,body, head) -> body, head
            | _ -> __unreachable__()

        let atoms = body @ [head]
        let positions, axioms = atoms |> List.mapi (x.procAtom clauseNum) |>
                                List.filter (fun p -> p.IsSome) |> List.map Option.get |>  List.unzip
        let axioms = axioms |> List.concat

        // process rule
        let clauseName = "clause" + clauseNum.ToString()
        let atomsVars = atoms |> List.map x.CollectFreeVarsInAtom |> List.map (List.sort) |>
                        List.filter (fun xs -> not (List.isEmpty xs))
        let clauseVars = x.CollectFreeVarsInAtoms atoms |> Set.ofList |> Set.toList |> List.sort
        let clauseVarsTerms = clauseVars |> List.map TIdent
        let clauseSorts = clauseVars |> List.map snd
        let clauseDecls, cRecord = x.generateAutomataDeclarations clauseName clauseSorts

        let clauseLen = List.length positions
        let prodName = "prod" + clauseLen.ToString()

        let prodOp =
            let ss = List.init clauseLen (fun _ -> stateSort)
            Operation.makeElementaryOperationFromSorts prodName ss stateSort

        let initAxiom =
            let l = cRecord.initConst
            let inits = List.map (fun r -> r.initConst) positions
            let r = TApply(prodOp, inits)
            rule [] [] (AApply(equal_op stateSort, [l; r]))
        let deltaAxiom =
            let stateVars = List.map (fun vars -> (List.init (pown m (List.length vars)) (fun _ -> (gensym(), stateSort)))) atomsVars
            let stateTerms = stateVars |> List.map (List.map TIdent)
            let atomsTerms = List.map (List.map TIdent) atomsVars
            let rs = List.map3 (fun r vs s -> TApply(r.delta, vs @ s) ) positions atomsTerms stateTerms
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

                let n = List.length clauseVars
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
            let rs,lastR = positions |> List.splitAt (clauseLen - 1)
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

        axioms @ clauseDecls @ List.map TransformedCommand tCommands

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
                let sorts = vars |> Seq.map snd
                let decls, record = x.generateAutomataDeclarations name (List.ofSeq sorts)
                (decls, (pat, record))
            let decls, patternToRecordMap = Seq.mapi2 f patternSet patternVars |> List.ofSeq |> List.unzip
            List.concat decls, Map.ofList patternToRecordMap
        let patternAxioms = seq {
            for KeyValue(pat, patRec) in patternToRecordMap do
                let namedPattern = Pattern(patRec.name, pat.terms)
                yield! (x.generatePatternAxioms namedPattern patRec pat.baseAutomata)
        }
        let automataRules = patternedRules |> List.map (List.map (fun p -> Map.find p patternToRecordMap))


        rules |> List.mapi x.procRule |> List.concat

    member private x.declareProds maxArity =
        seq {
            for i in [1..maxArity] do
                let name = "prod" + i.ToString()
                let states = List.init i (fun _ -> stateSort)
                OriginalCommand (DeclareFun(name, states, stateSort))
        }

    member x.traverseCommands oCommands (rules : rule list)  =
        seq {
            yield OriginalCommand(DeclareSort(stateSort))
            yield! (x.parseDatatypes adts)
            // TODO: remove constant
            yield! (x.declareProds 2)
            yield! (x.processDeclarations oCommands)
            // TODO: remove ltlt debug
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
