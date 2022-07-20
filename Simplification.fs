module RInGen.Simplification
open SMTLIB2

let simplifyConditional isConstructor unpreferredSet qs conds substituteWithInHead =
    let conds, eqs = List.choose2 (function Equal(t1, t2) -> Choice2Of2(t1, t2) | a -> Choice1Of2 a) conds
    let eqs, unifier = Unifier.fromList Set.empty unpreferredSet isConstructor eqs
    match unifier with
    | None -> None
    | Some unifier ->
    let conds = List.map (Atom.substituteWith unifier) (List.map Equal eqs @ conds)
    let head = substituteWithInHead unifier
    let qs = Quantifiers.remove (unifier |> Map.toList |> List.map fst |> Set.ofList) qs
    Some (qs, conds, head)

let rec private simplifyBinary zero one constr t1 t2 =
    let rec iter = function
        | t1, t2 when t1 = t2 -> [one]
        | TApply(op1, ts1), TApply(op2, ts2) ->
            if op1 = op2 then List.zip ts1 ts2 |> List.collect iter else [zero]
        | t1t2 -> [constr t1t2]
    iter (t1, t2)

let private isDiseqOp diseqs op =
    opt {
        let! retType = Operation.argumentTypes op |> List.tryHead
        let! op' = Map.tryFind retType diseqs
        return op = op'
    } |> function Some true -> true | _ -> false

let private distinct diseqs (t1, t2) =
    let op = Map.find (Term.typeOf t1) diseqs
    AApply(op, [t1; t2])

let private simplifyAtom diseqs = function
    | Equal(t1, t2) -> simplifyBinary Bot Top Equal t1 t2 |> List.map FOLAtom |> FOL.folAnd
    | AApply(op, [t1; t2]) when isDiseqOp diseqs op -> simplifyBinary Top Bot (distinct diseqs) t1 t2 |> List.map FOLAtom |> FOL.folOr
    | Distinct(t1, t2) -> simplifyBinary Top Bot Distinct t1 t2 |> List.map FOLAtom |> FOL.folOr
    | a -> FOLAtom a

let private collectConditions = function
    | FOLOr xs ->
        let conds, heads = List.choose2 (function FOLNot(FOLAtom a) -> Choice1Of2 a | f -> Choice2Of2 f) xs
        conds, heads
    | f -> [], [f]

let private simplifyFormula diseqs qs f =
    let conds, heads = collectConditions f
    match simplifyConditional (fun _ -> true) Set.empty qs conds (fun unifier -> List.map (FOL.substituteWith unifier) heads) with
    | Some (qs, conds, heads) ->
        let f' = FOLOr (List.map (FOLAtom >> FOLNot) conds @ heads)
        Some (qs, FOL.bind (simplifyAtom diseqs) f')
    | None -> None

let private isDiseqAtom diseqs = function
    | AApply(op, _) -> isDiseqOp diseqs op
    | _ -> false

let private isDiseqDeclaration diseqs f =
    let conds, head = collectConditions f
    match head with
    | [FOLAtom a] -> isDiseqAtom diseqs a && List.forall (isDiseqAtom diseqs) conds
    | _ -> false

let private simplifyCommand diseqs = function
    | FOLAssertion(qs, f) when not <| isDiseqDeclaration diseqs f ->
        match simplifyFormula diseqs qs f with
        | Some f -> f |> FOLAssertion |> Some
        | None -> None
    | c -> Some c

let simplify diseqs commands = List.choose (simplifyCommand diseqs) commands