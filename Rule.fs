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
    let linearizedAtoms, equalVars =
        let helper acc a =
            match a with
            | Top | Bot as a -> a, [] @ acc
            | Equal(t1, t2) ->
                let ts', equalVars = Terms.linearizeVariables [t1; t2]
                match ts' with
                | t1' :: t2' :: [] -> Equal(t1', t2'), equalVars @ acc
                | _ -> __unreachable__()
            | Distinct(t1, t2) ->
                let ts', equalVars = Terms.linearizeVariables [t1; t2]
                match ts' with
                | t1' :: t2' :: [] -> Distinct(t1', t2'), equalVars @ acc
                | _ -> __unreachable__()
            | AApply(op, ts) ->
                let ts', equalVars = Terms.linearizeVariables ts
                AApply(op, ts'), equalVars @ acc
        List.mapFold helper [] (head :: body)
    
    let eqVarsToEqAtoms = function
        | [] -> []
        | v::vs -> List.map (fun newVar -> Equal(TIdent(v), TIdent(newVar))) vs
        
    let equalities =  List.collect eqVarsToEqAtoms equalVars
    let head, atoms = List.uncons linearizedAtoms
    clARule (atoms @ equalities) head
