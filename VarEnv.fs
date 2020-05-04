module FLispy.VarEnv
open FLispy.Operations

module VarEnv =
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
