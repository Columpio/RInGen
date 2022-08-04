[<AutoOpen>]
module RInGen.Terms
open System.Collections.Generic
open SMTLIB2

module Term =
    let truth = TConst("true", BoolSort)
    let falsehood = TConst("false", BoolSort)

    let fromBool b = if b then truth else falsehood

    let apply op xs = TApply(op, xs)
    let apply0 op = apply op []
    let apply1 op t = apply op [t]
    let apply2 op x y = apply op [x; y]
    let apply3 op x y z = apply op [x; y; z]

    let generateVariable sort = TIdent <| SortedVar.freshFromSort sort
    let generateVariableWithPrefix vs = TIdent <| SortedVar.freshFromVar vs

    let isIdent = function
        | TIdent _ -> true
        | _ -> false

    let typeOf = function
        | TConst(_, typ)
        | TIdent(_, typ) -> typ
        | TApply(op, _) -> Operation.returnType op

    let tName = function
        | TConst(name, _)
        | TIdent(name, _) -> name
        | TApply(op, _) -> Operation.opName op

    let rec bind f = function
        | TIdent(name, typ)
        | TConst(name, typ) as t -> f t (name, typ)
        | TApply(op, ts) ->
            let ts = List.map (bind f) ts
            TApply(op, ts)

    let substituteWith substMap = bind (fun t vs -> Option.defaultValue t <| Map.tryFind vs substMap)

    let substituteWithPair v t u =
        let rec substInTermWithPair = function
            | TConst _ as c -> c
            | TIdent(v1, s1) as vs1 -> if v = (v1, s1) then t else vs1
            | TApply(op, ts) -> TApply(op, List.map substInTermWithPair ts)
        substInTermWithPair u

    let foldWithDepth fIdent fOpname fConst =
        let rec foldWithDepth depth z = function
            | TIdent(i, s) -> fIdent (i, s) depth z
            | TApply(op, ts) -> List.fold (foldWithDepth (depth + 1)) (fOpname op depth z) ts
            | TConst(name, typ) -> fConst (name, typ) depth z
        foldWithDepth 0

    let fold fIdent fOpname fConst =
        let rec fold z = function
            | TIdent(i, s) -> fIdent (i, s) z
            | TApply(op, ts) -> List.fold fold (fOpname op z) ts
            | TConst(name, typ) -> fConst (name, typ) z
        fold

    let map fIdent fOpname fConst =
        let rec map = function
            | TIdent(i, s) -> fIdent (i, s)
            | TApply(op, ts) -> TApply(fOpname op, List.map map ts)
            | TConst(name, typ) -> fConst (name, typ)
        map

    let mapFold fIdent fOpname fConst =
        let rec iter z = function
            | TIdent(i, s) ->
                let is', z = fIdent (i, s) z
                TIdent(is'), z
            | TApply(op, ts) ->
                let op, z = fOpname op z
                let ts, z = List.mapFold iter z ts
                TApply(op, ts), z
            | TConst(name, typ) ->
                let nt', z = fConst (name, typ) z
                TConst(nt'), z
        iter

    let foldVars f = fold f (fun _ -> id) (fun _ -> id)
    let foldVarsWithDepth f = foldWithDepth f (fun _ _ -> id) (fun _ _ -> id)
    let mapVars f = map f id TConst
    let mapFoldVars f = mapFold f (fun op map -> op, map) (fun nt z -> nt, z)

    let collectFreeVars = foldVars Set.add Set.empty >> Set.toList
    let collectFreeVarsCounter = foldVars Counter.add Counter.empty

    let tryCut = function
        | TApply(opname, args) -> Some(opname, args)
        | _ -> None

    let cut t = t |> tryCut |> Option.defaultWith (fun () -> failwith $"cannot get constructor and arguments of {t}")

    let private trySubstituteIdent map ident = Map.findOrApply TIdent map ident

    let instantiate instantiator = mapVars (trySubstituteIdent instantiator)

    let rewrite substConstrs instantiator =
        map (trySubstituteIdent instantiator) (Map.findOrDefault substConstrs) TConst

    let substitute constrMap varMap = map (trySubstituteIdent varMap) (Map.findOrDefault constrMap) TConst

    let depth = foldWithDepth (fun _ -> max) (fun _ d -> max (d + 1)) (fun _ -> max) 0

    type Uniformizer () =
        let mutable n = 0
        let varMap = Dictionary()
        let newIndex n = $"x%d{n}"
        member x.Uniformize =
            let substInIdent (i, s) =
                let n = Dictionary.getOrInitWith i varMap (fun () -> let newN = n in n <- n + 1; newN)
                TIdent(newIndex n, s)
            mapVars substInIdent

module Terms =
    let mapFold = List.mapFold
    let map = List.map

    let length = List.length
    let collectFreeVars = List.collect Term.collectFreeVars >> List.unique
    let numVars ts = collectFreeVars ts |> List.length
    let generateVariablesFromVars vars = List.map Term.generateVariableWithPrefix vars
    let generateVariablesFromOperation = Operation.argumentTypes >> List.map Term.generateVariable

    let generateNVariablesOfSort n sort = List.init n (fun _ -> Term.generateVariable sort)

    let collectFreeVarsCounter = List.map Term.collectFreeVarsCounter >> Counter.unionMany

    let linearizeVariables ts =
        let oldVars =
            collectFreeVarsCounter ts
            |> Map.toList
            |> List.sortWith (fun (v1, _) (v2, _) -> SortedVar.compare v1 v2)
        let newVars =
            oldVars
            |> List.map (fun ((_, s) as v, n) -> v, v :: SortedVars.generateNVariablesOfSort (n-1) s |> List.rev |> Array.ofList)
            |> Dictionary.ofList
        let oldVarsCount = Dictionary.ofList oldVars
        let findNewVar oldV =
            let count = oldVarsCount.[oldV] - 1
            oldVarsCount.[oldV] <- count
            let newVar = newVars.[oldV].[count]
            TIdent newVar
        let ts' = List.map (Term.mapVars findNewVar) ts
        let equalVars = newVars |> Dictionary.toList |> List.map (snd >> List.ofArray)
        ts', equalVars

    let instantiate instantiator = List.map (Term.instantiate instantiator)

    let rewrite substConstrs instantiator = List.map (Term.rewrite substConstrs instantiator)

    let cutHeads = List.mapChoose Term.tryCut >> Option.map List.unzip
