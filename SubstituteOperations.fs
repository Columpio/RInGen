module RInGen.SubstituteOperations

open System.Runtime.CompilerServices

type private termArgumentFolding = LeftAssoc | RightAssoc
type private atomArgumentFolding = Chainable | Pairwise

let private termOperations =
    [
        "+", LeftAssoc
        "-", LeftAssoc
        "*", LeftAssoc
        "and", LeftAssoc
        "or", LeftAssoc
        "=>", RightAssoc
    ] |> List.map (fun (name, assoc) -> Map.find name elementaryOperations, assoc) |> Map.ofList
let private atomOperations =
    [
        "=", Chainable
        "<=", Chainable
        "<", Chainable
        ">=", Chainable
        ">", Chainable
        "distinct", Pairwise
    ] |> List.map (fun (name, assoc) -> Map.find name elementaryOperations, assoc) |> Map.ofList

type SubstituteOperations(relativizations, eqSubstitutor, diseqSubstitutor, constantMap) =
    let mutable wasSubstituted = false

    let searchInRelativizations op =
        match Map.tryFind op relativizations with
        | Some _ as r -> wasSubstituted <- true; r
        | None -> None

    let relativizationsSubstitutor op ts justSubstOp defaultResult =
        match searchInRelativizations op with
        | Some (op', true) ->
            let newVar, newVarIdent = IdentGenerator.generateReturnArgument op
            [newVar], [Relativization.relapply op' ts newVarIdent], newVarIdent
        | Some (op', false) -> [], [], justSubstOp op'
        | None -> [], [], defaultResult

    let substituteOperationsWithRelationsInTermApplication op ts =
        relativizationsSubstitutor op ts (fun op' -> TApply(op', ts)) (TApply(op, ts))

    let applyBinary op x y =
        let ts = [x; y]
        let vars, conds, result = substituteOperationsWithRelationsInTermApplication op ts
        (vars, conds), result

    let rec substituteOperationsWithRelationsInTerm = function
        | TConst(c, _) as t ->
            match constantMap c with
            | Some c' -> wasSubstituted <- true; [], [], c'
            | None -> [], [], t
        | TIdent(name, sort) as t ->
            relativizationsSubstitutor (identToUserOp name sort) [] userOpToIdent t
        | TApply(op, ts) ->
            let vars, conds, ts = substituteOperationsWithRelationsInTermList ts
            match Map.tryFind op termOperations with
            | Some assoc when List.length ts >= 2 ->
                let folder =
                    match assoc with
                    | LeftAssoc -> List.mapReduce
                    | RightAssoc -> List.mapReduceBack
                let vcs, t = folder (applyBinary op) ts
                let vss, css = List.unzip vcs
                vars @ List.concat vss, conds @ List.concat css, t
            | _ ->
                let appVars, appConds, app = substituteOperationsWithRelationsInTermApplication op ts
                vars @ appVars, conds @ appConds, app

    and substituteOperationsWithRelationsInTermList ts =
        let varss, condss, ts = ts |> List.map substituteOperationsWithRelationsInTerm |> List.unzip3
        List.concat varss, List.concat condss, ts

    let substituteOperationsWithRelationsInAtomApplication op ts =
        match searchInRelativizations op with
        | Some(op', _) -> wasSubstituted <- true; AApply(op', ts)
        | None -> AApply(op, ts)

    let rec substituteOperationsWithRelationsInAtom = function
        | Top | Bot as a -> [], [], a
        | Equal(a, b) ->
            let avars, aconds, a = substituteOperationsWithRelationsInTerm a
            let bvars, bconds, b = substituteOperationsWithRelationsInTerm b
            let d = eqSubstitutor a b
            avars @ bvars, aconds @ bconds, d
        | Distinct(a, b) ->
            let avars, aconds, a = substituteOperationsWithRelationsInTerm a
            let bvars, bconds, b = substituteOperationsWithRelationsInTerm b
            let d = diseqSubstitutor a b
            avars @ bvars, aconds @ bconds, d
        | AApply(op, ts) ->
            let vars, conds, ts = substituteOperationsWithRelationsInTermList ts
            match Map.tryFind op atomOperations with
            | Some assoc when List.length ts >= 2 ->
                let makeApp =
                    match op with
                    | ElementaryOperation("=", _, _) -> (<||) eqSubstitutor
                    | ElementaryOperation("distinct", _, _) -> (<||) diseqSubstitutor
                    | _ -> fun (x, y) -> substituteOperationsWithRelationsInAtomApplication op [x; y]
                let pairs =
                    match assoc with
                    | Chainable -> List.pairwise
                    | Pairwise -> List.triangle
                match ts |> pairs |> List.map makeApp with
                | at::ats -> vars, ats @ conds, at
                | _ -> __unreachable__()
            | _ -> vars, conds, substituteOperationsWithRelationsInAtomApplication op ts

    let rec substInRule = function
        | BaseRule(premises, consequence) ->
            let pvss, pcss, ps = List.map substituteOperationsWithRelationsInAtom premises |> List.unzip3
            let cvs, ccs, c = substituteOperationsWithRelationsInAtom consequence
            rule (List.concat (cvs :: pvss)) (List.concat (ccs :: ps :: pcss)) c
        | ForallRule(vars, body) -> forallrule vars (substInRule body)
        | ExistsRule(vars, body) -> existsrule vars (substInRule body)

    new (relativizations) = SubstituteOperations(relativizations, emptyEqSubstitutor, smartDiseqSubstitutor, fun _ -> None)
    new (relativizations, constantMap) = SubstituteOperations(relativizations, emptyEqSubstitutor, smartDiseqSubstitutor, constantMap)
    new (relativizations, eqSubst, diseqSubst) =
        SubstituteOperations(relativizations, opSubstitutor emptyEqSubstitutor eqSubst, opSubstitutor smartDiseqSubstitutor diseqSubst, fun _ -> None)

    member x.WasSubstituted () = wasSubstituted

    member x.SubstituteOperationsWithRelations = function
        | TransformedCommand r -> substInRule r |> TransformedCommand
        | c -> c

type MapSorts<'acc>(mapSort : 'acc -> sort -> sort * 'acc, mapReturnSorts : bool) =
    let mapReturnSort sorts retSort = if mapReturnSorts then mapSort sorts retSort else retSort, sorts

    let mapSorts = List.mapFold mapSort

    let mapSortedVar sorts (name, sort) =
        let sort, sorts = mapSort sorts sort
        (name, sort), sorts

    let mapSortedVars = List.mapFold mapSortedVar

    let mapOp sorts =
        let mapOp constr name args ret =
            let args, sorts = mapSorts sorts args
            let ret, sorts = mapReturnSort sorts ret
            constr(name, args, ret), sorts
        function
        | UserDefinedOperation(name, args, ret) -> mapOp UserDefinedOperation name args ret
        | ElementaryOperation(name, args, ret) -> mapOp ElementaryOperation name args ret

    let rec mapTerm sorts = function
        | TConst _ as c -> c, sorts
        | TIdent(name, sort) ->
            let sort, sorts = mapSort sorts sort
            TIdent(name, sort), sorts
        | TApply(op, ts) ->
            let op, sorts = mapOp sorts op
            let ts, sorts = mapTerms sorts ts
            TApply(op, ts), sorts
    and mapTerms = List.mapFold mapTerm

    let rec mapAtom sorts = function
        | Top | Bot as a -> a, sorts
        | Equal(t1, t2) ->
            let t1, sorts = mapTerm sorts t1
            let t2, sorts = mapTerm sorts t2
            Equal(t1, t2), sorts
        | Distinct(t1, t2) ->
            let t1, sorts = mapTerm sorts t1
            let t2, sorts = mapTerm sorts t2
            Distinct(t1, t2), sorts
        | AApply(op, ts) ->
            let op, sorts = mapOp sorts op
            let ts, sorts = mapTerms sorts ts
            AApply(op, ts), sorts
    and mapAtoms = List.mapFold mapAtom

    let mapDatatype sorts (name, constrs) =
        let constrs, sorts =
            List.mapFold (fun sorts (name, vars) -> let vars, sorts = mapSortedVars sorts vars in (name, vars), sorts) sorts constrs
        (name, constrs), sorts

    let mapSortsInOrigCommand sorts = function
        | DeclareFun(name, argSorts, retSort) ->
            let argSorts, sorts = mapSorts sorts argSorts
            let retSort, sorts = mapReturnSort sorts retSort
            DeclareFun(name, argSorts, retSort), sorts
        | DeclareDatatype(name, constrs) ->
            let (name, constrs), sorts = mapDatatype sorts (name, constrs)
            DeclareDatatype(name, constrs), sorts
        | DeclareDatatypes dts ->
            let dts, sorts = List.mapFold mapDatatype sorts dts
            DeclareDatatypes dts, sorts
        | DeclareConst(name, sort) ->
            let retSort, sorts = mapSort sorts sort
            DeclareConst(name, retSort), sorts
        | c -> c, sorts

    let rec mapRule sorts = function
        | ForallRule(vars, body) ->
            let vars, sorts = mapSortedVars sorts vars
            let body, sorts = mapRule sorts body
            ForallRule(vars, body), sorts
        | ExistsRule(vars, body) ->
            let vars, sorts = mapSortedVars sorts vars
            let body, sorts = mapRule sorts body
            ExistsRule(vars, body), sorts
        | BaseRule(premises, conclusion) ->
            let premises, sorts = mapAtoms sorts premises
            let conclusion, sorts = mapAtom sorts conclusion
            BaseRule(premises, conclusion), sorts

    new (mapSort) = MapSorts(mapSort, true)

    member x.FoldOperation(sorts, op) = mapOp sorts op

    member x.FoldCommand sorts command =
        match command with
        | OriginalCommand c ->
            let c, sorts = mapSortsInOrigCommand sorts c
            OriginalCommand c, sorts
        | TransformedCommand r ->
            let r, sorts = mapRule sorts r
            TransformedCommand r, sorts

[<Extension>]
type Utils () =
    [<Extension>]
    static member inline MapCommand(x: MapSorts<unit>, command) = x.FoldCommand () command |> fst
    [<Extension>]
    static member inline MapOperation(x: MapSorts<unit>, op) = x.FoldOperation((), op) |> fst

[<AbstractClass>]
type TheorySubstitutor () =
    let substInCommand (mapper : MapSorts<unit>) (relativizer : SubstituteOperations) command =
        let command = relativizer.SubstituteOperationsWithRelations(command)
        let command = mapper.MapCommand(command)
        command

    abstract member MapReturnSortsFlag : bool
    default x.MapReturnSortsFlag = true
    abstract member TryMapSort : sort -> sort option
    abstract member GenerateDeclarations : unit -> transformedCommand list * sort * Map<operation,operation * bool> * (symbol -> term option)

    member x.SubstituteTheoryDelayed commands =
        let mutable wasMapped = false
        let mapSort () s =
            let rec mapSort s =
                match x.TryMapSort s with
                | Some s' -> wasMapped <- true; s'
                | None ->
                match s with
                | CompoundSort(name, sorts) -> CompoundSort(name, List.map mapSort sorts)
                | s -> s
            mapSort s, ()
        let preamble, newSort, newOps, newConstMap = x.GenerateDeclarations ()
        let mapper = MapSorts(mapSort, x.MapReturnSortsFlag)
        wasMapped <- false
        let relativizer = SubstituteOperations(newOps, newConstMap)
        let commands = List.map (substInCommand mapper relativizer) commands
        let wasSubstituted = relativizer.WasSubstituted ()
        let shouldAddPreamble = wasMapped || wasSubstituted
        let returnedCommands = if shouldAddPreamble then preamble @ commands else commands
        shouldAddPreamble, preamble, returnedCommands, newSort

    member x.SubstituteTheory commands = let _, _, commands, _ = x.SubstituteTheoryDelayed commands in commands
