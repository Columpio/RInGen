module FLispy.ParseToTerms
open FLispy.VarEnv
open FLispy.Operations
open FLispy.Typer

let private to_sorted_vars = List.map (function PList [PSymbol v; PSymbol s] -> v, s | _ -> __unreachable__())
let private to_var_binding = List.map (function PList [PSymbol v; t] -> v, t | _ -> __unreachable__())

let rec private toExpr ((typer, env) as te) = function
    | PNumber n -> Constant (Number n)
    | PSymbol "true" -> Constant (Bool true)
    | PSymbol "false" -> Constant (Bool false)
    | PList [] -> __unreachable__()
    | PList [PSymbol "let"; PList bindings; body] ->
        let handle_binding env (v, e) =
            let e = toExpr (typer, env) e
            let (v, _), env = VarEnv.extendOne env (v, typeOf e)
            (v, e), env
        let bindings = to_var_binding bindings
        let bindings, env = List.mapFold handle_binding env bindings
        let body = toExpr (typer, env) body
        Let(bindings, body)
    | PList [PSymbol "forall"; PList vars; body] ->
        let vars = to_sorted_vars vars
        let vars, env = VarEnv.extend env vars
        Forall(vars, toExpr (typer, env) body)
    | PList [PSymbol "exists"; PList vars; body] ->
        let vars = to_sorted_vars vars
        let vars, env = VarEnv.extend env vars
        Exists(vars, toExpr (typer, env) body)
    | PList (op::args) ->
        let args = List.map (toExpr te) args
        match op, args with
        | PSymbol "ite", [i; t; e] -> Ite(i, t, e)
        | PSymbol "and", _ -> And args
        | PSymbol "or", _ -> Or args
        | PSymbol "not", [arg] -> Not arg
        | PSymbol "=>", [i; t] -> Hence(i, t)
        | PSymbol f, args ->
            let op = getOperation f typer
            Apply(op, args)
        | e -> failwithf "%O" e
    | PSymbol x -> Ident(x, typeGet x te)
    | PMatch(t, cases) ->
        let t = toExpr te t
        let typ = typeOf t
        let extendEnvironment env = function
            | PSymbol v, typ ->
                let vt = (v, typ)
                match tryTypeCheck v typer with
                | Some _ -> Ident vt, env
                | None ->
                    let vt, env = VarEnv.extendOne env vt
                    Ident vt, env
            | _ -> __unreachable__()
        let handle_case (pat, body) =
            match pat with
            | PList (PSymbol constr::cargs) ->
                let op = getOperation constr typer
                let cargs, env = List.mapFold extendEnvironment env (List.zip cargs (Operation.argumentTypes op))
                Apply(op, cargs), toExpr (typer, env) body
            | _ ->
                let v, env = extendEnvironment env (pat, typ)
                v, toExpr (typer, env) body
        let cases = List.map handle_case cases
        Match(t, cases)

let parseToTerms exprs =
    let toComm typer e =
        let define_fun name vars sort body constr =
            let vars = to_sorted_vars vars
            let typer = Typer.addOperation name (Operation.makeUserOperationFromVars name vars sort) typer
            let env = VarEnv.create vars
            let body = toExpr (typer, env) body
            constr(name, vars, sort, body), typer
        let parse_constructors typer adtname constrs =
            let handle_constr typer = function
                | PList (PSymbol fname::vars) ->
                    let vars = to_sorted_vars vars
                    let typer = List.fold (fun typer (pr, s) -> Typer.addOperation pr (Operation.makeElementaryOperationFromSorts pr [adtname] s) typer) typer vars
                    let typer = Typer.addOperation fname (Operation.makeElementaryOperationFromVars fname vars adtname) typer
                    let testerName = "is-" + fname
                    let typer = Typer.addOperation testerName (Operation.makeElementaryOperationFromSorts testerName [adtname] "Bool") typer
                    (fname, vars), typer
                | _ -> __unreachable__()
            List.mapFold handle_constr typer constrs
        let comm, typer =
            match e with
            | PList [PSymbol "define-fun"; PSymbol name; PList vars; PSymbol sort; body] ->
                define_fun name vars sort body DefineFun
            | PList [PSymbol "define-fun-rec"; PSymbol name; PList vars; PSymbol sort; body] ->
                define_fun name vars sort body DefineFunRec
            | PList [PSymbol "define-funs-rec"; PList signs; PList bodies] ->
                let signs = signs |> List.map (function PList [PSymbol name; PList vars; PSymbol sort] -> name, to_sorted_vars vars, sort | _ -> __unreachable__())
                let typer = List.fold (fun typer (name, vars, sort) -> Typer.addOperation name (Operation.makeUserOperationFromVars name vars sort) typer) typer signs
                let fs = List.map2 (fun body (name, vars, sort) -> name, vars, sort, toExpr (typer, VarEnv.create vars) body) bodies signs
                DefineFunsRec fs, typer
            | PList [PSymbol "declare-datatype"; PSymbol adtname; PList constrs] ->
                let constrs, typer = parse_constructors typer adtname constrs
                DeclareDatatype(adtname, constrs), typer
            | PList [PSymbol "declare-datatypes"; PList signs; PList constr_groups] ->
                let names = signs |> List.map (function PList [PSymbol name; PNumber 0] -> name | _ -> __unreachable__())
                let dfs, typer = List.mapFold (fun typer (name, PList constrs) -> parse_constructors typer name constrs) typer (List.zip names constr_groups)
                DeclareDatatypes (List.zip names dfs), typer
            | PList [PSymbol "check-sat"] -> CheckSat, typer
            | PList [PSymbol "get-model"] -> GetModel, typer
            | PList (PSymbol "get-info"::args) ->
                args |> List.map (function PSymbol option -> option | _ -> __notImplemented__()) |> join " " |> GetInfo, typer
            | PList [PSymbol "assert"; expr] ->
                Assert(toExpr (typer, VarEnv.empty) expr), typer
            | PList [PSymbol "declare-sort"; PSymbol sort; PNumber 0] -> DeclareSort(sort), typer
            | PList [PSymbol "declare-const"; PSymbol name; PSymbol sort] ->
                DeclareConst(name, sort), Typer.addOperation name (Operation.makeElementaryOperationFromSorts name [] sort) typer
            | PList [PSymbol "declare-fun"; PSymbol name; PList argTypes; PSymbol sort] ->
                let argTypes = argTypes |> List.map (function PSymbol t -> t | _ -> __unreachable__())
                DeclareFun(name, argTypes, sort), Typer.addOperation name (Operation.makeElementaryOperationFromSorts name argTypes sort) typer
            | PList [PSymbol "set-logic"; PSymbol name] -> SetLogic(name), typer
            | e -> failwithf "%O" e
        comm, typer
    let comms, _ = List.mapFold toComm Typer.empty exprs
    comms
