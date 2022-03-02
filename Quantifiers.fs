[<AutoOpen>]
module RInGen.Quantifiers

module Quantifier =
    let negate = function
        | ForallQuantifier vars -> ExistsQuantifier vars
        | ExistsQuantifier vars -> ForallQuantifier vars
        | StableForallQuantifier _ as q -> q

    let getVars = function
        | ForallQuantifier vars
        | ExistsQuantifier vars
        | StableForallQuantifier vars -> vars

    let private unquantify = function
        | ForallQuantifier vars -> ForallQuantifier, vars
        | ExistsQuantifier vars -> ExistsQuantifier, vars
        | StableForallQuantifier vars -> StableForallQuantifier, vars

    let remove toRemove q =
        let qc, vars = unquantify q
        match List.filter (fun v -> not <| Set.contains v toRemove) vars with
        | [] -> None
        | vars -> Some <| qc vars

    let map f q =
        let qConstr, vars = unquantify q
        let vars = f vars
        qConstr vars

    let mapFold f z q =
        let qConstr, vars = unquantify q
        let vars, z = f z vars
        qConstr vars, z

    let withFreshVariables = mapFold SortedVars.withFreshVariables

module Quantifiers =

    let getVars = List.collect Quantifier.getVars

    let map f (qs : quantifiers) = List.map f qs

    let mapFold f z (qs : quantifiers) = List.mapFold f z qs

    let hasExists = List.exists (function ExistsQuantifier _ -> true | _ -> false)

    let (|ForallQuantifiersOrEmpty|_|) qs =
        List.foldChoose (fun vars -> function ForallQuantifier vars' | StableForallQuantifier vars' -> Some (vars @ vars') | _ -> None) [] qs

    let combine (outer : quantifiers) (inner : quantifiers) : quantifiers =
        match inner with
        | [] -> outer
        | _ ->
            let inner, innerLast = List.butLast inner
            inner @ Quantifiers.add innerLast outer

    let combineMany (qss : quantifiers list) : quantifiers =
        match qss with
        | [] -> Quantifiers.empty
        | qs::qss -> List.fold combine qs qss

    let forall vars : quantifiers = Quantifiers.add (ForallQuantifier vars) Quantifiers.empty
    let exists vars : quantifiers = Quantifiers.add (ExistsQuantifier vars) Quantifiers.empty
    let stableforall vars : quantifiers = Quantifiers.add (StableForallQuantifier vars) Quantifiers.empty

    let negate (qs : quantifiers) : quantifiers = List.map Quantifier.negate qs

    let withFreshVariables (qs : quantifiers) : quantifiers * Map<_,_> =
        mapFold Quantifier.withFreshVariables Map.empty qs

    let remove toRemove (qs : quantifiers) =
        List.foldBack (fun q qs -> match Quantifier.remove toRemove q with Some q -> Quantifiers.add q qs | None -> qs) qs Quantifiers.empty

    let simplify constr zero one e = function
        | [] -> e
        | vars -> if e = zero then zero elif e = one then one else constr(vars, e)
