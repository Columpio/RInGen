module FLispy.VarEnv
open FLispy.Typer
open FLispy.Operations

type sorted_var = string * sort
type env = Map<string, sort> * Map<string, string>

let empty : env = Map.empty, Map.empty

let get (env_sorts, env_vars) ((var, sort) as vs) : sorted_var =
    match Map.tryFind var env_sorts with
    | Some sort' when sort = sort' -> vs
    | Some sort' -> failwithf "Environment has sort %O of %O (%O)" sort' var sort
    | None ->
        match Map.tryFind var env_vars with
        | Some var' ->
            match Map.tryFind var' env_sorts with
            | Some sort' when sort = sort' -> var', sort
            | Some sort' -> failwithf "Environment has alias %O with sort %O for %O (%O)" var' sort' var sort
            | None -> failwithf "Environment has no sort for alias %O of %O (%O)" var' var sort
        | None -> failwithf "Environment has neither sort neither alias for %O (%O)" var sort

let extendOne (env_sorts, env_vars) ((var : string), sort) : sorted_var * env =
    let var', env_vars =
        if var.StartsWith("_") then
            let var' = gensym ()
            let env_vars = Map.add var var' env_vars
            var', env_vars
        elif Map.containsKey var env_sorts then
            let var' = gensymp var
            let env_vars = Map.add var var' env_vars
            var', env_vars
        else var, env_vars
    let env_sorts = Map.add var' sort env_sorts
    (var', sort), (env_sorts, env_vars)

let extend env vars = List.mapFold extendOne env vars
let create vars : env = vars |> extend empty |> snd

let private createFreshOne (env_sorts, env_vars) ((var : string), sort) : sorted_var * env =
    let var' = gensymp var
    let env_vars = Map.add var var' env_vars
    let env_sorts = Map.add var' sort env_sorts
    (var', sort), (env_sorts, env_vars)

let createFresh vars = List.mapFold createFreshOne empty vars

let typeCheck (env_sorts, env_vars) x =
    match Map.tryFind x env_sorts with
    | Some _ as t -> t
    | None ->
        match Map.tryFind x env_vars with
        | Some y -> Map.tryFind y env_sorts
        | None -> None

let typeGet x (typer, env) =
    match typeCheck env x with
    | Some t -> t
    | None ->
        match tryTypeCheck x typer with
        | Some t -> t
        | None -> failwithf "Unknown type: %s" x

let rec renameVars typer env = function
    | Ident(name, _) as e when Map.containsKey name typer -> e
    | Ident(name, sort) -> get env (name, sort) |> Ident
    | Apply(op, es) -> Apply(op, List.map (renameVars typer env) es)
    | Match(t, cases) ->
        let handleCase (pattern, expr) =
            let freeVars = MatchExtensions.getFreeVarsFromPattern typer pattern
            let _, env = extend env freeVars
            let pattern = renameVars typer env pattern
            let expr = renameVars typer env expr
            pattern, expr
        Match(renameVars typer env t, List.map handleCase cases)
    | Not e -> renameVars typer env e |> Not
    | Ite(i, t, e) -> Ite(renameVars typer env i, renameVars typer env t, renameVars typer env e)
    | Let(defs, body) ->
        let iter env (v, e) =
            let e = renameVars typer env e
            let (v, _), env = extendOne env (v, typeOf e)
            (v, e), env
        let defs, env = List.mapFold iter env defs
        Let(defs, renameVars typer env body)
    | Or es -> es |> List.map (renameVars typer env) |> Or
    | And es -> es |> List.map (renameVars typer env) |> And
    | Constant _ as e -> e
    | _ -> __notImplemented__()
