module RInGen.Rule

let private baseRule q fromAtoms toAtom =
    Rule(q, fromAtoms, toAtom)

let aerule forallVars existsVars fromAtoms toAtom =
    let forallVars = Terms.collectFreeVars forallVars
    let existsVars = Terms.collectFreeVars existsVars
    baseRule (Quantifiers.combine (Quantifiers.forall forallVars) (Quantifiers.exists existsVars)) fromAtoms toAtom

let private arule vars fromAtoms toAtom = baseRule (Quantifiers.forall vars) fromAtoms toAtom

let clARule fromAtoms toAtom =
    let freeVars = Atoms.collectFreeVars (toAtom :: fromAtoms)
    arule freeVars fromAtoms toAtom

let clAFact toAtom = clARule [] toAtom

let linearize (rule.Rule(_, body, head)) =
    let linearizedAtoms =
        let helper = function
            | Top | Bot as a -> a, Map.empty
            | Equal(t1, t2) ->
                let ts', vars2vars = Terms.linearizeVariables [t1; t2]
                match ts' with
                | t1' :: t2' :: [] -> Equal(t1', t2'), vars2vars
                | _ -> __unreachable__()
            | Distinct(t1, t2) ->
                let ts', vars2vars = Terms.linearizeVariables [t1; t2]
                match ts' with
                | t1' :: t2' :: [] -> Distinct(t1', t2'), vars2vars
                | _ -> __unreachable__()
            | AApply(op, ts) ->
                let ts', vars2vars = Terms.linearizeVariables ts
                AApply(op, ts'), vars2vars
        List.map helper (head :: body)
    let atoms, equalities = List.unzip linearizedAtoms
    let equalities = equalities |> List.collect (Map.toList)
                     |> List.map (fun (var1, var2) -> Equal(TIdent var1, TIdent var2) )
    let head, atoms = List.uncons atoms
    clARule (atoms @ equalities) head
