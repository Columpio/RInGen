module FLispy.UnfoldDeclarations

let rec private unfoldDeclarationsExpr = function
    | Hence(i, t) -> Or [Not (unfoldDeclarationsExpr i); unfoldDeclarationsExpr t]
    | And ts -> ts |> List.map unfoldDeclarationsExpr |> And
    | Or ts -> ts |> List.map unfoldDeclarationsExpr |> Or
    | Not t -> t |> unfoldDeclarationsExpr |> Not
    | Ite(i, t, e) -> Ite(unfoldDeclarationsExpr i, unfoldDeclarationsExpr t, unfoldDeclarationsExpr e)
    | Apply(op, ts) -> ts |> List.map unfoldDeclarationsExpr |> fun ts -> Apply(op, ts)
    | Ident _
    | Constant _ as e -> e
    | Exists(vs, t) -> Exists(vs, unfoldDeclarationsExpr t)
    | Forall(vs, t) -> Forall(vs, unfoldDeclarationsExpr t)
    | Let(assns, b) ->
        let assns = assns |> List.map (fun (v, e) -> v, unfoldDeclarationsExpr e)
        Let(assns, unfoldDeclarationsExpr b)
    | Match(t, cases) ->
        let cases = cases |> List.map (fun (v, e) -> v, unfoldDeclarationsExpr e)
        Match(unfoldDeclarationsExpr t, cases)

let private unfoldDeclarationsInDef (name, args, sort, body) = name, args, sort, unfoldDeclarationsExpr body

let private unfoldDeclarationsCommand = function
    | DeclareConst _
    | DeclareDatatype _
    | DeclareDatatypes _
    | DeclareFun _
    | DeclareSort _
    | CheckSat
    | SetLogic _
    | GetInfo _ as c -> c
    | Assert e -> unfoldDeclarationsExpr e |> Assert
    | DefineFun df -> df |> unfoldDeclarationsInDef |> DefineFun
    | DefineFunRec df -> df |> unfoldDeclarationsInDef |> DefineFunRec
    | DefineFunsRec dfs -> dfs |> List.map unfoldDeclarationsInDef |> DefineFunsRec

let unfoldDeclarations = List.map unfoldDeclarationsCommand
