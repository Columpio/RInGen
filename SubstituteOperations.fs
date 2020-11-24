module RInGen.SubstituteOperations

type SubstituteOperations(relativizations, eqSubstitutor, diseqSubstitutor, constantMap) =
    let relativizationsSubstitutor op ts justSubstOp defaultResult =
        match Map.tryFind op relativizations with
        | Some (op', true) ->
            let newVar, newVarIdent = IdentGenerator.generateReturnArgument op
            [newVar], [Relativization.relapply op' ts newVarIdent], newVarIdent
        | Some (op', false) -> [], [], justSubstOp op'
        | None -> [], [], defaultResult

    let rec substituteOperationsWithRelationsInTerm = function
        | TConst c as t -> [], [], constantMap c t
        | TIdent(name, sort) as t ->
            relativizationsSubstitutor (identToUserOp name sort) [] userOpToIdent t
        | TApply(op, ts) ->
            let vars, conds, ts = substituteOperationsWithRelationsInTermList ts
            let appVars, appConds, app = relativizationsSubstitutor op ts (fun op' -> TApply(op', ts)) (TApply(op, ts))
            vars @ appVars, conds @ appConds, app

    and substituteOperationsWithRelationsInTermList ts =
        let varss, condss, ts = ts |> List.map substituteOperationsWithRelationsInTerm |> List.unzip3
        List.concat varss, List.concat condss, ts

    let defaultFormula vars conds f =
        match vars, conds with
        | [], [] -> [], [], f
        | _ -> __notImplemented__()

    let ahence conds t =
        match conds with
        | [] -> t
        | _ -> AHence(AAnd conds, t)

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
            match Map.tryFind op relativizations with
            | Some(op', _) -> vars, conds, AApply(op', ts)
            | None -> vars, conds, AApply(op, ts)
        //TODO: relativization of general formula does not make sense
        | ANot a ->
            let vars, conds, a = substituteOperationsWithRelationsInAtom a
            defaultFormula vars conds (ANot a)
        | AAnd ts ->
            let vars, conds, ts = substituteOperationsWithRelationsInAtoms ts
            defaultFormula vars conds (AAnd ts)
        | AOr ts ->
            let vars, ts = ts |> List.map (fun t -> let vars, conds, t = substituteOperationsWithRelationsInAtom t in vars, ahence conds t) |> List.unzip
            List.concat vars, [], AOr ts
        | AHence(a, b) ->
            let avars, aconds, a = substituteOperationsWithRelationsInAtom a
            let bvars, bconds, b = substituteOperationsWithRelationsInAtom b
            defaultFormula (avars @ bvars) (aconds @ bconds) (AHence(a, b))
    and substituteOperationsWithRelationsInAtoms  ts =
        let varss, condss, ts = ts |> List.map substituteOperationsWithRelationsInAtom |> List.unzip3
        List.concat varss, List.concat condss, ts

    let rec substInRule = function
        | BaseRule(premises, consequence) ->
            let pvss, pcss, ps = List.map substituteOperationsWithRelationsInAtom premises |> List.unzip3
            let cvs, ccs, c = substituteOperationsWithRelationsInAtom consequence
            rule (List.concat (cvs :: pvss)) (List.concat (ccs :: ps :: pcss)) c
        | ForallRule(vars, body) -> forallrule vars (substInRule body)
        | ExistsRule(vars, body) -> existsrule vars (substInRule body)

    new (relativizations) = SubstituteOperations(relativizations, emptyEqSubstitutor, smartDiseqSubstitutor, drop)
    new (relativizations, constantMap) = SubstituteOperations(relativizations, emptyEqSubstitutor, smartDiseqSubstitutor, constantMap)
    new (relativizations, eqSubst, diseqSubst) =
        SubstituteOperations(relativizations, opSubstitutor emptyEqSubstitutor eqSubst, opSubstitutor smartDiseqSubstitutor diseqSubst, drop)

    member x.SubstituteOperationsWithRelations = function
        | TransformedCommand r -> substInRule r |> TransformedCommand
        | c -> c
