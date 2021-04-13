module RInGen.VarEnv
open RInGen.Typer
open RInGen.Operations

type sorted_var = ident * sort
type env = Map<ident, sort> * Map<ident, ident>

let empty : env = Map.empty, Map.empty

let tryGetFromEnv ((env_sorts, env_vars) : env) ((var, sort) as vs : sorted_var) : sorted_var option =
    let var' =
        match Map.tryFind var env_vars with
        | Some var' -> var'
        | None -> var
    match Map.tryFind var' env_sorts with
    | Some sort' when sort = sort' -> Some (var', sort)
    | Some sort' -> None // failwithf "Environment has alias %O with sort %O for %O (%O)" var' sort' var sort
    | None -> None // failwithf "Environment has no sort for alias %O of %O (%O)" var' var sort

let get (typer : Typer, env) (name, _ as vs : sorted_var) : sorted_var =
    match tryGetFromEnv env vs with
    | Some vs' -> vs'
    | None when typer.containsKey name -> vs
    | None -> failwithf $"Identifier is not found in the environment: {vs}"

let extendOne ((typer, (env_sorts, env_vars)) : Typer * env) ((var : ident), sort) : sorted_var * (Typer * env) =
    let var', env_vars =
        if var = "_" then // ADT match placeholder
            let var' = IdentGenerator.gensym ()
            let env_vars = Map.add var var' env_vars
            var', env_vars
        elif Map.containsKey var env_sorts || typer.containsKey var then
            let var' = IdentGenerator.gensymp var
            let env_vars = Map.add var var' env_vars
            var', env_vars
        else var, env_vars
    let env_sorts = Map.add var' sort env_sorts
    (var', sort), (typer, (env_sorts, env_vars))

let extend te vars = List.mapFold extendOne te vars
let create typer vars = vars |> extend (typer, empty) |> snd

let replaceOne ((typer, (env_sorts, env_vars)) : 'a * env) ((var : symbol), sort) : 'a * env =
    let env_vars = Map.add var var env_vars
    let env_sorts = Map.add var sort env_sorts
    typer, (env_sorts, env_vars)

let replace te vars = List.fold replaceOne te vars

let private typeCheck (env_sorts, env_vars) x =
    match Map.tryFind x env_sorts with
    | Some _ as t -> t
    | None ->
        match Map.tryFind x env_vars with
        | Some y -> Map.tryFind y env_sorts
        | None -> None

let typeGet (x : ident) (typer, env) =
    match typeCheck env x with
    | Some t -> t
    | None ->
        match tryTypeCheck x typer with
        | Some t -> t
        | None -> failwithf $"Unknown type: {x}"
