module FLispy.TakeOutQuantifiers
open FLispy.Operations

let private forallk vars Q = forall vars << Q
let private existsk vars Q = exists vars << Q
let private emptyQuantifier = id

let takeOutQuantifiers ts e =
    let rec takeOutQs env = function
        | Forall(vars, e) ->
            let vars = Typer.sorted_var_list ts vars
            let vars, env = VarEnv.extend env vars
            let Q, env, e = takeOutQs env e
            forallk vars Q, env, e
        | Exists(vars, e) ->
            let vars = Typer.sorted_var_list ts vars
            let vars, env = VarEnv.extend env vars
            let Q, env, e = takeOutQs env e
            existsk vars Q, env, e
        | And es ->
            let es, (Q, env) = takeOutQuantifiersFromExprList env es
            Q, env, And es
        | Or es ->
            let es, (Q, env) = takeOutQuantifiersFromExprList env es
            Q, env, Or es
        | Not e ->
            let Q, env, e = takeOutQs env e
            Q, env, Not e
        | Hence(e1, e2) ->
            let Q1, env, e1 = takeOutQs env e1
            let Q2, env, e2 = takeOutQs env e2
            Q1 >> Q2, env, Hence(e1, e2)
        | Match _
        | Let _
        | Apply _ as e -> emptyQuantifier, env, VarEnv.renameVars ts env e
        | _ -> __unreachable__()
    and takeOutQuantifiersFromExprList env =
        List.mapFold (fun (Q, env) e -> let Q', env', e' = takeOutQs env e in e', (Q >> Q', env')) (emptyQuantifier, env)
    takeOutQs VarEnv.empty e
