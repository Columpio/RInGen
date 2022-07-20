[<AutoOpen>]
module RInGen.Atoms
open SMTLIB2

module Atom =
    let apply op xs = AApply(op, xs)
    let apply1 op x = apply op [x]
    let apply2 op x y = apply op [x; y]

    let mapFold f z = function
        | Top
        | Bot as a -> a, z
        | Equal(t1, t2) ->
            let t1, z = f z t1
            let t2, z = f z t2
            Equal(t1, t2), z
        | Distinct(t1, t2) ->
            let t1, z = f z t1
            let t2, z = f z t2
            Distinct(t1, t2), z
        | AApply(op, ts) ->
            let ts, z = Terms.mapFold f z ts
            AApply(op, ts), z

    let map f = function
        | Top
        | Bot as a -> a
        | Equal(t1, t2) ->
            let t1 = f t1
            let t2 = f t2
            Equal(t1, t2)
        | Distinct(t1, t2) ->
            let t1 = f t1
            let t2 = f t2
            Distinct(t1, t2)
        | AApply(op, ts) ->
            let ts = Terms.map f ts
            AApply(op, ts)

    let substituteWith freshVarsMap = map (Term.substituteWith freshVarsMap)

    let tryGetPredicate = function
       | AApply(op, _) -> Some op
       | _ -> None

    let tryGetArguments = function
       | AApply(_, ts) -> Some ts
       | Equal(t1, t2) | Distinct(t1, t2) -> Some [t1; t2]
       | Bot | Top -> None

    let collectFreeVars = tryGetArguments >> Option.defaultValue [] >> Terms.collectFreeVars

module Atoms =
    let map = List.map
    let mapFold = List.mapFold

    let collectFreeVars = List.collect Atom.collectFreeVars >> List.unique

module Conditional =
    let toCondition x : 'a conditional = [], x

    let pair ((conds1, x1) : term conditional) ((conds2, x2) : term conditional) : (term * term) conditional = conds1 @ conds2, (x1, x2)
    let list (cnds : 'a conditional list) : ('a list) conditional =
        let cnds, xs = List.unzip cnds
        List.concat cnds, xs
    let mapHead f ((conds, x) : 'a conditional) : 'b conditional = conds, f x
    let strengthen conds1 ((conds2, x) : 'a conditional) : 'a conditional = conds1 @ conds2, x
    let bind f ((conds1, x) : 'a conditional) : 'b conditional =
        let conds2, y = f x
        conds1 @ conds2, y
    let map2 f ((conds1, x) : 'a conditional) ((conds2, y) : 'b conditional) = conds1 @ conds2, f x y
    let toConj ((conds, x) : atom conditional) : atom conjunction = Conjunction <| x :: conds

    let map fConds mapChild ((conds, a) : 'a conditional) : 'b conditional =
        Atoms.map fConds conds, mapChild a

    let mapFold fConds mapFoldChild z ((conds, a) : 'a conditional) : 'a conditional * _ =
        let conds, z = Atoms.mapFold fConds z conds
        let a, z = mapFoldChild z a
        (conds, a), z

    let substituteWith freshVarsMap = map (Atom.substituteWith freshVarsMap)
