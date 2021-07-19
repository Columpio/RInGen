module RInGen.SubstituteOperations

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
        | TConst c as t ->
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
