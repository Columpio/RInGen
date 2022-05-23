[<AutoOpen>]
module RInGen.FOL

module FOL =
    let apply op xs = FOLAtom <| Atom.apply op xs
    let apply1 op x = apply op [x]
    let apply2 op x y = apply op [x; y]

    let rec folNot = function
        | FOLNot f -> f
        | FOLAtom a -> notMapApply (fun op ts -> AApply(op, ts) |> FOLAtom |> FOLNot) FOLAtom a
        | f -> FOLNot f
    let folOr = simplBinary (FOLAtom Bot) (FOLAtom Top) (function FOLOr xs -> Some xs | _ -> None) FOLOr
    let folAnd = simplBinary (FOLAtom Top) (FOLAtom Bot) (function FOLAnd xs -> Some xs | _ -> None) FOLAnd

    let hence a b = folOr [folNot a; b]

    let (|Rule|_|) = function
        | FOLOr ats ->
            match List.choose2 (function FOLNot(FOLAtom n) -> Choice2Of2 n | a -> Choice1Of2 a) ats with
            | [FOLAtom head], body -> Some(body, head)
            | _ -> None
        | _ -> None

    let map f =
        let rec iter = function
            | FOLAtom a -> FOLAtom (f a)
            | FOLNot f -> f |> iter |> FOLNot
            | FOLAnd fs -> fs |> List.map iter |> FOLAnd
            | FOLOr fs -> fs |> List.map iter |> FOLOr
            | FOLEq(a, b) -> FOLEq(iter a, iter b)
        iter

    let bind f =
        let rec iter = function
            | FOLAtom a -> f a
            | FOLNot f -> f |> iter |> FOLNot
            | FOLAnd fs -> fs |> List.map iter |> folAnd
            | FOLOr fs -> fs |> List.map iter |> folOr
            | FOLEq(a, b) -> FOLEq(iter a, iter b)
        iter

    let fold f z =
        let rec iter z = function
            | FOLAtom a -> f z a
            | FOLNot f -> iter z f
            | FOLAnd fs
            | FOLOr fs -> List.fold iter z fs
            | FOLEq(a, b) ->
                let z' = iter z a
                iter z' b
        iter z

    let mapFold f z =
        let rec iter z = function
            | FOLAtom a ->
                let a', z' = f z a
                FOLAtom a', z'
            | FOLNot f ->
                let f', z' = iter z f
                FOLNot f', z'
            | FOLAnd fs ->
                let fs', z' = List.mapFold iter z fs
                FOLAnd fs', z'
            | FOLOr fs ->
                let fs', z' = List.mapFold iter z fs
                FOLOr fs', z'
            | FOLEq(a, b) ->
                let a', z' = iter z a
                let b', z'' = iter z' b
                FOLEq(a', b'), z''
        iter z

    let mapFoldPositivity f pos z =
        let rec iter pos z = function
            | FOLAtom a ->
                let a', z' = f pos z a
                a', z'
            | FOLNot f ->
                let f', z' = iter (not pos) z f
                FOLNot f', z'
            | FOLAnd fs ->
                let fs', z' = List.mapFold (iter pos) z fs
                FOLAnd fs', z'
            | FOLOr fs ->
                let fs', z' = List.mapFold (iter pos) z fs
                FOLOr fs', z'
            | FOLEq(a, b) ->
                let a', z' = iter pos z a
                let b', z'' = iter pos z' b
                FOLEq(a', b'), z''
        iter pos z

    let private collectFreeVarsWith free fol = fold (fun free atom -> Atom.collectFreeVars atom |> Set.ofList |> Set.union free) free fol
    let collectFreeVars fol = collectFreeVarsWith Set.empty fol |> Set.toList
    let collectFreeVarsOfList fols = List.fold collectFreeVarsWith Set.empty fols |> Set.toList

    let substituteWith freshVarsMap = map (Atom.substituteWith freshVarsMap)

module Lemma =
    let withFreshVariables ((qs, cond) : lemma) =
        let qs, freshVarsMap = Quantifiers.withFreshVariables qs
        let freshVarsMap = Map.map (fun _ -> TIdent) freshVarsMap
        let cond = Conditional.substituteWith freshVarsMap (FOL.substituteWith freshVarsMap) cond
        qs, cond

module FOLCommand =
    let private aequivalence vars fromAtom toAtom = FOLAssertion(Quantifiers.forall vars, FOLEq(fromAtom, toAtom))
    let private arule vars body head = FOLAssertion(Quantifiers.forall vars, FOL.hence body head)
    let private afact vars head = FOLAssertion(Quantifiers.forall vars, FOLAtom head)

    let (|Rule|_|) = function
        | FOLAssertion(qs, FOL.Rule(body, head)) -> Some(qs, body, head)
        | _ -> None

    let fromTransformed = function
        | TransformedCommand(rule.Rule(qs, body, head)) -> FOLAssertion(qs, FOLOr ((FOLAtom head) :: (List.map (FOLAtom >> FOLNot) body)))
        | OriginalCommand c -> FOLOriginalCommand c
        | LemmaCommand _ -> __unreachable__()

    let clAEquivalence body head =
       let freeVars = Atoms.collectFreeVars (head :: body)
       aequivalence freeVars (FOL.folAnd <| List.map FOLAtom body) (FOLAtom head)

    let clAxor body head =
       let freeVars = Atoms.collectFreeVars (head :: body)
       aequivalence freeVars (FOL.folAnd <| List.map FOLAtom body) (FOL.folNot <| FOLAtom head)

    let clAEquivalenceFromFOL body head =
       let freeVars = FOL.collectFreeVarsOfList (head :: body)
       aequivalence freeVars (FOL.folAnd body) head

    let clARule body head =
       let freeVars = Atoms.collectFreeVars (head :: body)
       arule freeVars (FOL.folAnd <| List.map FOLAtom body) (FOLAtom head)

    let clAFact head =
        let freeVars = Atom.collectFreeVars head
        afact freeVars head

    let folAssert (qs, e) =
        match e with
        | FOLAtom Top -> None
        | _ -> Some (FOLAssertion(qs, e))

module FOLCommands =
    let fromTransformed = List.map FOLCommand.fromTransformed

module Conj =
    let singleton x = Conjunction [x]
    let exponent (Conjunction cs : 'a disjunction conjunction) : 'a conjunction disjunction =
        List.map (function Disjunction cs -> cs) cs |> List.product |> List.map Conjunction |> Disjunction
    let map produce_disjunction (Conjunction dss) =
        List.map (produce_disjunction >> Disjunction) dss |> Conjunction
    let bind (produce_disjunction : atom -> atom list) =
        map (function Disjunction ds -> List.collect produce_disjunction ds)
    let flatten (Conjunction css : 'a conjunction conjunction) = List.collect (function Conjunction cs -> cs) css |> Conjunction
    let toFOL (Conjunction cs : atom conjunction) = cs |> List.map FOLAtom |> FOL.folAnd

module Disj =
    let singleton x = Disjunction [x]
    let get (Disjunction d) = d
    let map f (Disjunction ds) = List.map f ds |> Disjunction
    let exponent (Disjunction cs : 'a conjunction disjunction) : 'a disjunction conjunction =
        List.map (function Conjunction cs -> cs) cs |> List.product |> List.map Disjunction |> Conjunction
    let disj dss = List.collect (function Disjunction ds -> ds) dss |> Disjunction
    let conj (dss : 'a conjunction disjunction list) =
        let css = Conj.exponent (Conjunction dss)
        let cs = map Conj.flatten css
        cs
    let union (Disjunction d1) (Disjunction d2) = Disjunction (d1 @ d2)

module DNF =
    let empty : dnf = Disjunction [Conjunction []]
    let singleton : atom -> dnf = Conj.singleton >> Disj.singleton
    let flip (Disjunction cs : dnf) : cnf = cs |> List.map (function Conjunction cs -> Disjunction cs) |> Conjunction
    let toFOL (Disjunction cs : dnf) = cs |> List.map Conj.toFOL |> FOL.folOr

[<Struct>]
type CollectBuilder =
    member __.Bind(xs, binder) = List.collect binder xs
    member __.Bind(Disjunction dss : dnf, binder) = List.collect (function Conjunction cs -> binder cs) dss
    member __.Return(value) = [value]
    member __.ReturnFrom(value) = value
let collector = CollectBuilder()
