module RInGen.PrintToProlog
open SMTLIB2

let private arithmeticOperations = Operations.arithmeticOperations |> List.map (fun (a, _, n) -> a, n) |> Map.ofList

(*
:- type nat ---> z ; s(nat).

:- pred incorrect.
:- pred inc(nat, nat).
:- pred dec(nat, nat).

inc(z, s(z)).
inc(s(X), s(Y)) :- inc(X, Y).

dec(s(z), z).
dec(s(X), s(Y)) :- dec(X, Y).

incorrect :- inc(X, Y), dec(X, Y).
*)
let private queryName = "incorrect" // this is hardcoded in VeriMAP-iddt (we will never obtain this term as all our idents are of the form `[a-zA-Z]+_[0-9]+`
let private mapName (s : string) = String.toLowerFirstChar s
let private mapNames = List.map mapName
let private mapVariable (s : string) = String.toUpperFirstChar s
let private mapSort = function
    | IntSort -> "int"
    | BoolSort -> "bool"
    | ADTSort s -> mapName s
    | _ -> __notImplemented__()
let private mapSorts = List.map mapSort

let private mapOp = function
    | ElementaryOperation(name, _, _) ->
        Map.tryFind name arithmeticOperations |> Option.defaultValue (mapName name, false)
    | UserDefinedOperation(name, _, _) -> mapName name, false

let rec private mapApply vars op ts =
    match mapOp op, mapTerms vars ts with
    | (op, true), [t1; t2] -> $"(%s{t1} %s{op} %s{t2})"
    | (_, true), _ -> __unreachable__()
    | (op, false), [] -> op
    | (op, false), ts -> ts |> join ", " |> sprintf "%s(%s)" op

and private mapTerm vars = function
    | TConst(name, _) -> mapName name
    | TIdent(name, _) -> if Set.contains name vars then mapVariable name else mapName name
    | TApply(op, ts) -> mapApply vars op ts
and private mapTerms vars = List.map (mapTerm vars)

let private mapAtomInPremise vars = function
    | Top -> None
    | Bot -> Some queryName
    | AApply(op, ts) -> mapApply vars op ts |> Some
    | Equal(t1, t2) -> $"%s{mapTerm vars t1} = %s{mapTerm vars t2}" |> Some
    | Distinct(t1, t2) -> $"%s{mapTerm vars t1} =\= %s{mapTerm vars t2}" |> Some
let private mapAtomInHead vars a =
    match mapAtomInPremise vars a with
    | None ->
        match a with
        | Bot -> Some queryName
        | _ -> None
    | a -> a

let private mapRule vars premises head =
    match vars with
    | Quantifiers.ForallQuantifiersOrEmpty vars ->
        let vars = vars |> List.map fst |> Set.ofList
        let premises = List.choose (mapAtomInPremise vars) premises
        match mapAtomInHead vars head with
        | None -> None
        | Some head ->
            let clause =
                match premises with
                | [] -> head
                | _ -> premises |> join ", " |> sprintf "%s :- %s" head
            Some $"%s{clause}."
    | _ -> None

let private mapDatatypeDeclaration adtDef =
    let name, cs = ADTExtensions.adtDefinitionToRaw adtDef
    let handleConstr (constr, selectors) =
        let constr = mapName constr
        let sorts = selectors |> List.map (snd >> mapSort)
        match sorts with
        | [] -> constr
        | _ -> sorts |> join ", " |> sprintf "%s(%s)" constr
    let name = mapSort name
    let cs = List.map handleConstr cs
    cs |> join "; " |> sprintf ":- type %s ---> %s." name

let private mapPredicateDeclaration name args =
    let name = mapName name
    let args = mapSorts args
    let def =
        match args with
        | [] -> name
        | _ -> args |> join ", " |> sprintf "%s(%s)" name
    $":- pred %s{def}."

let private mapOriginalCommand = function
    | DeclareDatatype dt -> [mapDatatypeDeclaration dt]
    | DeclareDatatypes dts -> List.map mapDatatypeDeclaration dts
    | DeclareFun(name, args, BoolSort) -> [mapPredicateDeclaration name args]
    | DeclareConst(name, BoolSort) -> [mapPredicateDeclaration name []]
    | _ -> []

let private mapTransformedCommand = function
    | FOLOriginalCommand cmnd -> mapOriginalCommand cmnd
    | FOLCommand.Rule(qs, body, head) -> mapRule qs body head |> Option.toList
    | _ -> __unreachable__()

let isFirstOrderPrologProgram commands =
    let hasSortDecls = List.exists (function FOLOriginalCommand (DeclareSort _) -> true | _ -> false) commands
    let allAreRules = List.forall (function FOLOriginalCommand _ | FOLCommand.Rule _ -> true | _ -> false) commands
    not hasSortDecls && allAreRules

let toPrologFile commands =
    let preamble = mapPredicateDeclaration queryName []
    let commands = List.collect mapTransformedCommand commands
    preamble :: commands
