module RInGen.TtaTransform

open Microsoft.FSharp.Collections
open RInGen.IdentGenerator
open FOLCommand
open Operations

let stateSortName = gensymp "State"
let stateSort = FreeSort stateSortName
let notop = Operation.makeElementaryRelationFromSorts "not" [BoolSort]

let ordSortedVar (sv1 : sorted_var) (sv2 : sorted_var) =
    let sort1 = snd sv1
    let sort2 = snd sv2
    let cmpSorts = Sort.compare sort1 sort2
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

let getBotSymbol sort =
    Sort.sortToFlatString sort + "_bot"

type Processer(adts : datatype_def list) =
    let m = adts |> List.collect snd |> List.map (thd3 >> List.length) |> List.max
    member private x.getEqRelName s =
        "eq" + s.ToString()
    member private x.getDiseqRelName s =
        "diseq" + s.ToString()

    member private x.extractPattern atom =
        let name, terms =
            match atom with
            | Top | Bot -> None, []
            | Distinct(t1, t2) ->
                let sort = Term.typeOf t1
                Some (x.getDiseqRelName sort), [t1; t2]
            | Equal(t1, t2) ->
                let sort = Term.typeOf t1
                Some (x.getEqRelName sort), [t1; t2]
            | AApply(op, ts) -> Some (Operation.opName op), ts
        match name with
        | None -> None
        | Some name ->
            let vars = Terms.collectFreeVars terms
            let renameMap = Terms.generateVariablesFromVars vars |> List.zip vars |> Map.ofList
            let renamedTerms = List.map (Term.substituteWith renameMap) terms
            let _, baseAutomata =
                let sorts = terms |> List.map Term.typeOf
                x.generateAutomataDeclarations name sorts
            Some {baseAutomata = baseAutomata; terms=renamedTerms}

    member private x.generateAutomataDeclarations name sortList =
        let initStateName = "init_" + name
        let isFinalName = "isFinal_" + name
        let deltaName = "delta_" + name
        let reachName = "reach_" + name
        let statesVec =
            let n = List.length sortList
            List.init (pown m n) (fun _ -> stateSort)

        let decls =
            let initStateDecl = DeclareConst(initStateName, stateSort)
            let isFinalDecl = DeclareFun(isFinalName, [stateSort], BoolSort)
            let deltaDecl = DeclareFun(deltaName, sortList @ statesVec, stateSort)
            let reachDecl = DeclareFun(reachName, [stateSort], BoolSort)
            [initStateDecl; isFinalDecl; deltaDecl; reachDecl]

        let aRec =
            let initState = TConst(initStateName, stateSort)
            let isFinal = Operation.makeElementaryRelationFromSorts isFinalName [stateSort]
            let delta = Operation.makeElementaryOperationFromSorts deltaName (sortList @ statesVec) stateSort
            let reach = Operation.makeElementaryRelationFromSorts reachName [stateSort]
            {name=name; initConst = initState; isFinal = isFinal; delta = delta; reach=reach}

        List.map FOLOriginalCommand decls, aRec

    member private x.processDeclarations oCommands =
        let getDecls = function
            | DeclareFun(fname, args, _) -> x.generateAutomataDeclarations fname args |> fst
            | _ -> []
        List.collect getDecls oCommands

    member private x.parseDatatypes adts =
        let processDt(sName, xs) =
            let s = ADTSort sName
            let constructors = List.map (fun (c, _, _) -> DeclareConst (Operation.opName c, s)) xs
            let bot = DeclareConst(getBotSymbol s, s)
            let baseDecls =
                 List.map FOLOriginalCommand ([DeclareSort(sName); bot] @ constructors)
            // eq axioms
            let automataDecls, eqRec =
                let eqRelName = x.getEqRelName s
                x.generateAutomataDeclarations eqRelName [s; s]

            let initAxiom =
                let r = Atom.apply1 eqRec.isFinal eqRec.initConst
                clAFact r
            let deltaAxiom =
                let qTerms = Terms.generateNVariablesOfSort (pown m 2) stateSort
                let fVar, gVar = ("f", s), ("g", s)
                let fTerm, gTerm = TIdent fVar, TIdent gVar
                let l = AApply(eqRec.isFinal, [TApply(eqRec.delta, [fTerm; gTerm] @ qTerms)])
                let r =
                    let rl = AApply(equal_op s, [fTerm; gTerm])
                    let qDiag = List.init m (fun i -> qTerms.[i*(m+1)])
                    let rr = List.map (fun v -> AApply(eqRec.isFinal, [v])) qDiag
                    rl :: rr
                clAEquivalence r l

            // TODO: diseq + diseqAxioms ??
            // Note : diseq decls are generated twice, see parseDeclarations
            baseDecls @ automataDecls @ [initAxiom; deltaAxiom]

        List.collect processDt adts

    member private x.procRule clauseNum (Rule(_, body, head)) patAutomata =
        let atoms = head :: body

        // process rule
        let clauseName = "clause" + clauseNum.ToString()
        let atomsVars = atoms |> List.map Atom.collectFreeVars |> List.map (List.sortWith ordSortedVar)
        let clauseVars = Atoms.collectFreeVars atoms |> List.unique |> List.sortWith ordSortedVar
        let clauseVarsTerms = clauseVars |> List.map TIdent
        let clauseSorts = clauseVars |> List.map snd
        let clauseDecls, cRecord = x.generateAutomataDeclarations clauseName clauseSorts

        let clauseLen = List.length patAutomata
        let prodName = "prod_" + clauseName

        let prodDecl, prodOp =
            let ss = List.init clauseLen (fun _ -> stateSort)
            let op = Operation.makeElementaryOperationFromSorts prodName ss stateSort
            let decl = FOLOriginalCommand (DeclareFun(prodName, ss, stateSort))
            decl, op
        let clauseDecls = prodDecl::clauseDecls

        let initAxiom =
            let l = cRecord.initConst
            let inits = List.map (fun r -> r.initConst) patAutomata
            let r = TApply(prodOp, inits)
            clAFact (Atom.apply2 (equal_op stateSort) l r)
        let deltaAxiom =
            let stateTerms = List.map (fun vars -> (Terms.generateNVariablesOfSort (pown m (List.length vars)) stateSort)) atomsVars
            let atomsTerms = List.map (List.map TIdent) atomsVars
            let rs = List.map3 (fun r vs s -> TApply(r.delta, vs @ s)) patAutomata atomsTerms stateTerms
            let r = TApply(prodOp, rs)
            let l =
                // helper functions
                let genQMask aVars = List.map (fun v -> List.contains v aVars) clauseVars
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
                let stateTerms = statePositions |> List.map (fun positions -> List.map2 List.item positions stateTerms)
                let lStates = List.map (fun qs -> TApply(prodOp, qs)) stateTerms
                TApply(cRecord.delta, clauseVarsTerms @ lStates)
            clAFact (AApply(equal_op stateSort, [l; r]))
        let finalAxiom =
            let stateTerms = Terms.generateNVariablesOfSort clauseLen stateSort
            let li = TApply(prodOp, stateTerms)
            let l = AApply(cRecord.isFinal, [li])
            let rs, lastR = List.butLast patAutomata
            let states, lastStates = stateTerms |> List.splitAt (clauseLen - 1)
            let rs = List.map2 (fun r q -> AApply(r.isFinal, [q]) ) rs states
            // head isFinal is negated
            let lastR =
                match head with
                | Bot ->
                    AApply(lastR.isFinal, lastStates)
                | _ ->
                    AApply(notop, [TApply(lastR.isFinal, lastStates)])
            clAEquivalence (lastR :: rs) l
        let reachInit =
            clAFact (AApply(cRecord.reach, [cRecord.initConst]))
        let reachDelta =
            let qTerms = Terms.generateNVariablesOfSort (pown m (List.length clauseVarsTerms)) stateSort
            let l = List.map (fun q -> AApply(cRecord.reach, [q])) qTerms
            let r =
                let ri = TApply(cRecord.delta, clauseVarsTerms @ qTerms)
                AApply(cRecord.reach, [ri])
            clARule l r
        let condition =
            let qVar = ("q", stateSort)
            let qTerm = TIdent qVar
            let l = AApply(cRecord.reach, [qTerm])
            let r = AApply(notop, [TApply(cRecord.isFinal, [qTerm])])
            clARule [l] r
        let tCommands = [initAxiom; deltaAxiom; finalAxiom; reachInit; reachDelta; condition]

        clauseDecls @ tCommands

    member private x.generatePatternAxioms (p:namedPattern) (patRec:AutomataRecord) (baseRec:AutomataRecord) =
        // not implemented
        // will return list of rules
        // TODO: have to pass m as param
        []

    member private x.procRules rules =
//        let querries, rules = List.choose2 (function | Rule(_,_,head) as r -> match head with | Bot -> Choice1Of2 r | _ -> Choice2Of2 r) rules
        let patternedRules = List.map (function Rule(_, body, head) -> List.choose x.extractPattern (head :: body)) rules

        let patternSet = patternedRules |> List.concat |> List.unique
        let patternVars = patternSet |> List.map (fun p -> Terms.collectFreeVars p.terms)
        let decls, patternToRecordMap =
            let f i pat vars =
                let name = "P" + i.ToString()
                let sorts = vars |> Seq.map snd |> List.ofSeq |> List.sortWith Sort.compare
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
            yield FOLOriginalCommand(DeclareSort(stateSortName))
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
