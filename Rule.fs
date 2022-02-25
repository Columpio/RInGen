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
