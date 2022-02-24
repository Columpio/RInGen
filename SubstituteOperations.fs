module RInGen.SubstituteOperations

open System.Runtime.CompilerServices
open Operations

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
        "<=", Chainable
        "<", Chainable
        ">=", Chainable
        ">", Chainable
    ] |> List.map (fun (name, assoc) -> Map.find name elementaryOperations, assoc) |> Map.ofList

type FormulaTraverser () =
    abstract TraverseSort : sort -> sort
    default x.TraverseSort (sort : sort) = sort

    abstract TraverseReturnSort : sort -> sort
    default x.TraverseReturnSort (sort : sort) = sort

    member x.TraverseSorts sorts = List.map x.TraverseSort sorts

    member x.TraverseSortedVar (name, sort) =
        let sort = x.TraverseSort sort
        (name, sort)

    member x.TraverseSortedVars vars = List.map x.TraverseSortedVar vars

    member x.TraverseOp op =
        let mapOp constr name args ret =
            let args = x.TraverseSorts args
            let ret = x.TraverseReturnSort ret
            constr(name, args, ret)
        match op with
        | UserDefinedOperation(name, args, ret) -> mapOp UserDefinedOperation name args ret
        | ElementaryOperation(name, args, ret) -> mapOp ElementaryOperation name args ret

    member x.TraverseTerm = function
        | TConst _ as c -> c
        | TIdent(name, sort) ->
            let sort = x.TraverseSort sort
            TIdent(name, sort)
        | TApply(op, ts) ->
            let op = x.TraverseOp op
            let ts = x.TraverseTerms ts
            TApply(op, ts)
    member x.TraverseTerms terms = List.map x.TraverseTerm terms

    member x.TraverseAtom = function
        | Bot | Top as a -> a
        | Equal(t1, t2) ->
            let t1 = x.TraverseTerm t1
            let t2 = x.TraverseTerm t2
            Equal(t1, t2)
        | Distinct(t1, t2) ->
            let t1 = x.TraverseTerm t1
            let t2 = x.TraverseTerm t2
            Distinct(t1, t2)
        | AApply(op, ts) ->
            let op = x.TraverseOp op
            let ts = x.TraverseTerms ts
            AApply(op, ts)
    member x.TraverseAtoms atoms = List.map x.TraverseAtom atoms

    member x.TraverseDatatype (name, constrs) =
        let mapConstrEntry (c, t, ss) =
            let c' = x.TraverseOp c
            let t' = x.TraverseOp c
            let ss' = List.map x.TraverseOp ss
            (c', t', ss')
        let constrs = List.map mapConstrEntry constrs
        (name, constrs)

    member x.TraverseQuantifiers = Quantifiers.map (Quantifier.map x.TraverseSortedVars)

    member x.TraverseRule r =
        let rArgs =
            match r with
            | Rule(qs, premises, conclusion)
            | Equivalence(qs, premises, conclusion) ->
                let qs = x.TraverseQuantifiers qs
                let premises = x.TraverseAtoms premises
                let conclusion = x.TraverseAtom conclusion
                (qs, premises, conclusion)
        match r with
        | Rule _ -> Rule rArgs
        | Equivalence _ -> Equivalence rArgs

    member x.TraverseFOLFormula = FOL.map x.TraverseAtom

    member x.TraverseLemma (qs, (premises, lemma)) =
        let qs = x.TraverseQuantifiers qs
        let premises = x.TraverseAtoms premises
        let lemma = x.TraverseFOLFormula lemma
        (qs, (premises, lemma))

    member x.TraverseCommand = function
        | DeclareFun(name, argSorts, retSort) ->
            let argSorts = x.TraverseSorts argSorts
            let retSort = x.TraverseReturnSort retSort
            DeclareFun(name, argSorts, retSort)
        | DeclareDatatype(name, constrs) ->
            let (name, constrs) = x.TraverseDatatype (name, constrs)
            command.DeclareDatatype(name, constrs)
        | DeclareDatatypes dts ->
            let dts = List.map x.TraverseDatatype dts
            command.DeclareDatatypes dts
        | DeclareConst(name, sort) ->
            let retSort = x.TraverseSort sort
            DeclareConst(name, retSort)
        | c -> c

    member x.TraverseTransformedCommand command =
        match command with
        | OriginalCommand c ->
            let c = x.TraverseCommand c
            OriginalCommand c
        | TransformedCommand r ->
            let r = x.TraverseRule r
            TransformedCommand r
        | LemmaCommand(pred, vars, bodyLemma, headCube) ->
            let vars = x.TraverseSortedVars vars
            let bodyLemma = x.TraverseLemma bodyLemma
            let headCube = x.TraverseLemma headCube
            LemmaCommand(pred, vars, bodyLemma, headCube)

type SubstituteOperations(relativizations, eqSubstitutor, diseqSubstitutor, constantMap) =
    let mutable wasSubstituted = false

    let searchInRelativizations op =
        match Map.tryFind op relativizations with
        | Some _ as r -> wasSubstituted <- true; r
        | None -> None

    let relativizationsSubstitutor op ts justSubstOp defaultResult =
        let generateReturnArgument op =
            let retType = Operation.returnType op
            let retArg = IdentGenerator.gensym (), retType
            let retVar = TIdent retArg
            retArg, retVar
        match searchInRelativizations op with
        | Some (op', true) ->
            let newVar, newVarIdent = generateReturnArgument op
            ([newVar], [Relativization.relapply op' ts newVarIdent]), newVarIdent
        | Some (op', false) -> ([], []), justSubstOp op'
        | None -> ([], []), defaultResult

    let substituteOperationsWithRelationsInTermApplication op ts =
        relativizationsSubstitutor op ts (fun op' -> TApply(op', ts)) (TApply(op, ts))

    let rec substituteOperationsWithRelationsInTerm = function
        | TIdent _ as t -> [], [], t
        | TConst(c, _) as t ->
            match constantMap c with
            | Some c' -> wasSubstituted <- true; [], [], c'
            | None -> [], [], t
        | TApply(op, ts) ->
            let vars, conds, ts = substituteOperationsWithRelationsInTermList ts
            let top = termOperations
            match Map.tryFind op termOperations with
            | Some assoc when List.length ts >= 2 ->
                let folder =
                    match assoc with
                    | LeftAssoc -> List.mapReduce
                    | RightAssoc -> List.mapReduceBack
                let vcs, t = folder (fun x y -> substituteOperationsWithRelationsInTermApplication op [x; y]) ts
                let vss, css = List.unzip vcs
                vars @ List.concat vss, conds @ List.concat css, t
            | _ ->
                let (appVars, appConds), app = substituteOperationsWithRelationsInTermApplication op ts
                vars @ appVars, conds @ appConds, app

    and substituteOperationsWithRelationsInTermList ts =
        let varss, condss, ts = ts |> List.map substituteOperationsWithRelationsInTerm |> List.unzip3
        List.concat varss, List.concat condss, ts

    let substituteOperationsWithRelationsInAtomApplication op ts =
        match searchInRelativizations op with
        | Some(op', _) -> wasSubstituted <- true; AApply(op', ts)
        | None -> AApply(op, ts)

    let substituteOperationsWithRelationsInAtomWithPositivity posK k (oldVars, oldConds) a =
        let a', (newVars, newConds) =
            match a with
            | Top | Bot as a -> k a, ([], [])
            | Equal(a, b) ->
                let avars, aconds, a = substituteOperationsWithRelationsInTerm a
                let bvars, bconds, b = substituteOperationsWithRelationsInTerm b
                let d = posK diseqSubstitutor eqSubstitutor a b
                d, (avars @ bvars, aconds @ bconds)
            | Distinct(a, b) ->
                let avars, aconds, a = substituteOperationsWithRelationsInTerm a
                let bvars, bconds, b = substituteOperationsWithRelationsInTerm b
                let d = posK eqSubstitutor diseqSubstitutor a b
                d, (avars @ bvars, aconds @ bconds)
            | AApply(op, ts) ->
                let vars, conds, ts = substituteOperationsWithRelationsInTermList ts
                opt {
                    if List.length ts <= 1 then return! None else
                    let! assoc, makeApp =
                        match Map.tryFind op atomOperations, op with
                        | Some assoc, _ -> Some (assoc, fun (x, y) -> substituteOperationsWithRelationsInAtomApplication op [x; y])
                        | _, Equality -> Some(Chainable, (<||) eqSubstitutor)
                        | _, Disequality -> Some(Pairwise, (<||) diseqSubstitutor)
                        | _ -> None
                    let pairs =
                        match assoc with
                        | Chainable -> List.pairwise
                        | Pairwise -> List.triangle
                    match ts |> pairs |> List.map makeApp with
                    | at::ats -> return k at, (vars, ats @ conds)
                    | _ -> __unreachable__()
                } |> Option.defaultWith (fun () -> k <| substituteOperationsWithRelationsInAtomApplication op ts, (vars, conds))
        a', (newVars @ oldVars, newConds @ oldConds)

    let substituteOperationsWithRelationsInAtom = substituteOperationsWithRelationsInAtomWithPositivity (fun _ -> id) id
    let substituteOperationsWithRelationsInAtoms = List.mapFold substituteOperationsWithRelationsInAtom ([], [])

    let rec substInRule qs premises consequence =
        let ps, vcs = substituteOperationsWithRelationsInAtoms premises
        let c, (vars, conds) = substituteOperationsWithRelationsInAtom vcs consequence
        Rule(Quantifiers.combine qs (Quantifiers.forall vars), ps @ conds, c)

    let substituteOperationsWithRelationsInFOL =
        let posK pos dualSubst subst a b = if pos then subst a b |> FOLAtom else dualSubst a b |> FOLAtom |> FOLNot
        FOL.mapFoldPositivity (fun pos -> substituteOperationsWithRelationsInAtomWithPositivity (posK pos) FOLAtom)

    let substInLemma pos (qs, (premises, lemma)) =
        let ps, vcs = substituteOperationsWithRelationsInAtoms premises
        let c, (newVars, newConds) = substituteOperationsWithRelationsInFOL pos vcs lemma
        Quantifiers.combine qs (Quantifiers.forall newVars), (ps @ newConds, c)

    new (relativizations) = SubstituteOperations(relativizations, emptyEqSubstitutor, smartDiseqSubstitutor, fun _ -> None)
    new (relativizations, constantMap) = SubstituteOperations(relativizations, emptyEqSubstitutor, smartDiseqSubstitutor, constantMap)
    new (relativizations, eqSubst, diseqSubst) =
        SubstituteOperations(relativizations, opSubstitutor emptyEqSubstitutor eqSubst, opSubstitutor smartDiseqSubstitutor diseqSubst, fun _ -> None)

    member x.WasSubstituted () = wasSubstituted

    member x.SubstituteOperationsWithRelations = function
        | TransformedCommand(Rule(qs, body, head)) -> substInRule qs body head |> TransformedCommand
        | LemmaCommand(pred, vars, bodyLemma, headCube) ->
            let bodyLemma = substInLemma true bodyLemma
            let headCube = substInLemma false headCube
            LemmaCommand(pred, vars, bodyLemma, headCube)
        | c -> c

type MapSorts<'acc>(mapSort : 'acc -> sort -> sort * 'acc, mapReturnSorts : bool) =
    inherit FormulaTraverser ()
    let mutable acc = Unchecked.defaultof<'acc>

    override x.TraverseSort sort =
        let sort', acc' = mapSort acc sort
        acc <- acc'
        sort'

    override x.TraverseReturnSort sort = if mapReturnSorts then x.TraverseSort sort else sort

    member x.FoldCommand acc' command =
        acc <- acc'
        let command' = x.TraverseTransformedCommand command
        command', acc
    
    new (mapSort) = MapSorts(mapSort, true)

[<AbstractClass>]
type TheorySubstitutor () =
    inherit FormulaTraverser ()
    let mutable wasMapped = false

    member x.SubstInCommand (relativizer : SubstituteOperations) command =
        let command = relativizer.SubstituteOperationsWithRelations(command)
        let command = x.TraverseTransformedCommand(command)
        command

    override x.TraverseSort s =
        let rec mapSort s =
            match x.TryMapSort s with
            | Some s' -> wasMapped <- true; s'
            | None ->
            match s with
            | ArraySort(s1, s2) -> ArraySort(mapSort s1, mapSort s2)
            | s -> s
        mapSort s

    override x.TraverseReturnSort sort = if x.MapReturnSortsFlag then x.TraverseSort sort else sort

    abstract member MapReturnSortsFlag : bool
    default x.MapReturnSortsFlag = true
    abstract member TryMapSort : sort -> sort option
    abstract member GenerateDeclarations : unit -> transformedCommand list * sort * Map<operation,operation * bool> * (symbol -> term option)

    member x.SubstituteTheoryDelayed commands =
        let preamble, newSort, newOps, newConstMap = x.GenerateDeclarations ()
        let relativizer = SubstituteOperations(newOps, newConstMap)
        let commands = List.map (x.SubstInCommand relativizer) commands
        let wasSubstituted = relativizer.WasSubstituted ()
        let shouldAddPreamble = wasMapped || wasSubstituted
        let returnedCommands = if shouldAddPreamble then preamble @ commands else commands
        shouldAddPreamble, preamble, returnedCommands, newSort

    member x.SubstituteTheory commands = let _, _, commands, _ = x.SubstituteTheoryDelayed commands in commands
