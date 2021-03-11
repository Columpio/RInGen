module RInGen.PrintToProlog

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
let private mapName (s : string) = s.ToLowerFirstChar()
let private mapNames = List.map mapName
let private mapVariable (s : string) = s.ToUpperFirstChar()
let private mapSort = function
    | PrimitiveSort s -> mapName s
    | _ -> __notImplemented__()
let private mapSorts = List.map mapSort

let private mapOp = function
    | ElementaryOperation(name, _, _)
    | UserDefinedOperation(name, _, _) -> mapName name

let rec private mapTerm vars = function
    | TConst name -> mapName name
    | TIdent(name, _) -> if Set.contains name vars then mapVariable name else mapName name
    | TApply(op, ts) ->
        let op = mapOp op
        let ts = mapTerms vars ts
        ts |> join ", " |> sprintf "%s(%s)" op
and private mapTerms vars = List.map (mapTerm vars)

let private mapAtomInPremise vars = function
    | Bot -> Some queryName
    | Top -> None
    | AApply(op, ts) ->
        let op = mapOp op
        let ts = mapTerms vars ts
        ts |> join ", " |> sprintf "%s(%s)" op |> Some
    | Equal(t1, t2) -> sprintf "%s = %s" (mapTerm vars t1) (mapTerm vars t2) |> Some
    | Distinct(t1, t2) -> sprintf "%s =\= %s" (mapTerm vars t1) (mapTerm vars t2) |> Some
let private mapAtomInHead vars a =
    match mapAtomInPremise vars a with
    | None ->
        match a with
        | Bot -> Some queryName
        | _ -> None
    | a -> a

let rec private mapRule vars = function
    | ExistsRule _ -> None
    | ForallRule(vars', r) -> mapRule (vars @ vars') r
    | BaseRule(premises, head) ->
        let vars = vars |> List.map fst |> Set.ofList
        let premises = List.choose (mapAtomInPremise vars) premises
        match mapAtomInHead vars head with
        | None -> None
        | Some head ->
            let clause =
                match premises with
                | [] -> head
                | _ -> premises |> join ", " |> sprintf "%s :- %s" head
            Some (sprintf "%s." clause)

let private mapDatatypeDeclaration (name, cs) =
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
    sprintf ":- pred %s." def

let private mapFunctionDeclaration name args ret =
    if ret <> boolSort then None else Some [mapPredicateDeclaration name args]

let private mapOriginalCommand = function
    | DeclareDatatype(name, cs) -> Some [mapDatatypeDeclaration (name, cs)]
    | DeclareDatatypes dts -> Some <| List.map mapDatatypeDeclaration dts
    | DeclareFun(name, args, ret) -> mapFunctionDeclaration name args ret
    | DeclareConst(name, sort) -> mapFunctionDeclaration name [] sort
    | _ -> None

let private mapTransformedCommand = function
    | OriginalCommand cmnd -> mapOriginalCommand cmnd
    | TransformedCommand r -> mapRule [] r |> Option.map List.singleton

let toPrologFile commands =
    let preamble = mapPredicateDeclaration queryName []
    let commands = List.choose mapTransformedCommand commands |> List.concat
    preamble :: commands
