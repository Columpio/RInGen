module FLispy.Runtime

open System.Collections.Generic

let rec toString x = x.ToString()
//    function
//    | Number n -> n.ToString()
//    | Symbol s -> s
//    | Match(term, cases) -> cases |> List.map (fun (a, b) -> List [a; b]) |> toStringList |> sprintf "(match %s %s)" (toString term)
//    | List xs -> toStringList xs
and toStringList = List.map toString >> join " " >> sprintf "(%s)"

//let declare_sort typename = List [Symbol "declare-sort"; typename; Number 0]
//let declare_fun name argTypes retType = List [Symbol "declare-fun"; Symbol name; List argTypes; retType]
//let declare_rel name argTypes = declare_fun name argTypes (Symbol "Bool")
//let ite cond thenBranch elseBranch = List [Symbol "ite"; cond; thenBranch; elseBranch]
//let equal t1 t2 = List [Symbol "="; t1; t2]
//let asserte expr = List [Symbol "assert"; expr]
//let forall vars expr = List [Symbol "forall"; List vars; expr]
//let pair (a, b) = List [a; b]
//let hence e1 e2 = List [Symbol "=>"; e1; e2]
//let ande args = List (Symbol "and" :: args)
//let call f args = List (f::args)
//let falsee = Symbol "false"

let to_sorts = function
    | DeclareDatatype(typename, constructors) ->
        let parse_constructor (name, args) = DeclareFun(name, List.map snd args, typename)
        let decsort = DeclareSort typename
        let decfuns = List.map parse_constructor constructors
        decsort::decfuns
    | e -> [e]

//type Relation(name, args, retType, body) =
//    let retArg = if retType = Symbol "Bool" then None else Some (gensym(), retType)
//    let args = optCons (get_args_and_types args) retArg
//    let declaration = args |> List.map snd |> declare_rel name
//    
//    member x.Declaration = declaration
//    member x.NewReturnVar () =
//        match retArg with
//        | Some (_, argType) -> Some (gensym (), argType)
//        | None -> None
//    member x.ReturnType = retType
//    member x.Body = body
//    member x.TypedArguments = args
//    member x.Arguments = args |> List.map fst
//    member x.Name = Symbol name
//    member x.AssumptionsToBody(assumptions, retExpr) =
//        match retArg with
//        | Some (retArg, _) -> (equal retArg retExpr) :: assumptions
//        | None -> retExpr :: assumptions
//let NullRelation = Relation("", [], Symbol "Bool", Symbol "")
//
//type Typer() =
//    let constructors = Dictionary<_, _>()
//    let relations = Dictionary<_, Relation>()
//    member x.GetTypeSignature(constr) = constructors.Item(constr)
//    member x.HasConstructor(constr) = constructors.ContainsKey(constr)
//    member x.AddConstructor = function
//        | Symbol s -> constructors.Add(s, [])
//        | List (Symbol s::args) -> constructors.Add(s, get_adt_type_sign args)
//        | _ -> __unreachable__()
//    member x.AddRelation(name, rel) = relations.Add(name, rel)
//    member x.GetRelation(name) = relations.Item(name)
//    member x.TryGetRelation(name) =
//        let out = ref NullRelation
//        if relations.TryGetValue(name, out) then Some !out else None
//    member x.RelHasReturnType(name, typ) =
//        match x.TryGetRelation(name) with
//        | Some rel -> rel.ReturnType = typ
//        | None -> false

//let get_free_vars (typer : Typer) expr =
//    let rec get_free_vars = function
//        | List (Symbol constr::args), _ ->
//            typer.GetTypeSignature(constr)
//            |> List.map Some
//            |> List.zip args
//            |> List.collect get_free_vars
//        | Symbol s, _ when typer.HasConstructor(s) -> []
//        | Symbol _ as s, Some argType -> [s, argType]
//        | _ -> __notImplemented__()
//    get_free_vars (expr, None)

let exprToClauses (typer : Typer) expr =
    let rec exprToClauses = function
        | Match(term, cases) ->
            let handle_case (pattern, body) =
                let pat_match = equal term pattern
                let vars = get_free_vars typer pattern
                exprToClauses body
                |> List.map (fun (vars', assumptions, body) -> vars @ vars', pat_match::assumptions, body)
            List.collect handle_case cases
        | Let(bindings, body) ->
            let vars = List.map fst bindings
            let assumptions = List.map (fun (v, e) -> equal v e) bindings
            exprToClauses body
            |> List.map (fun (vars', assumptions', body') -> vars @ vars', assumptions @ assumptions', body')
        | List (Symbol name as sname::callargs) ->
            let args = callargs |> List.map exprToClauses
            let args = args |> List.map (function [a] -> a | l -> failwithf "big list! %O" l)
            let vars = List.collect fst3 args
            let assumptions = List.collect snd3 args
            let args = List.map thd3 args
            match typer.TryGetRelation(name) with
            | Some rel ->
                match rel.NewReturnVar () with
                | Some ((retArg, _) as retVar) ->
                    let expr = call sname (retArg::args)
                    Some [(retVar::vars), (expr::assumptions), retArg]
                | None -> None
            | None when name = "=" ->
                match args with
                | [List (Symbol p::_) as p1; p2] ->
                    if typer.RelHasReturnType(p, Symbol "Bool")
                    then Some [vars, p1::assumptions, p2]
                    else None
                | _ -> None
            | None -> None
            |> Option.defaultValue ([vars, assumptions, call sname args])
        | Number _
        | Symbol _ as e -> [[], [], e]
        | e -> failwithf "toclauses4: %O" e
    exprToClauses expr

let to_clause (typer : Typer) = function
    | DefineFun(name, args, retType, body)
    | DefineFunRec(name, args, retType, body) ->
        let rel = typer.GetRelation(name)
        let handle_clause (vars, assumptions, body) =
            let vars = (List.map pair (rel.TypedArguments @ vars))
            let body = rel.AssumptionsToBody(assumptions, body)
            asserte (forall vars (hence (ande body) (call rel.Name rel.Arguments)))
        let bodies =
            exprToClauses typer rel.Body
            |> List.map handle_clause
        rel.Declaration::bodies
    | Assert(Not(Forall(forall_vars, expr))) ->
        let clauses = exprToClauses typer expr
        match clauses with
        | [(vars, assumptions, body)] ->
            let vars = forall_vars @ List.map pair vars
//            [asserte (forall vars (hence (ande (body::assumptions)) falsee))]
            [asserte (hence (forall vars (ande (body::assumptions))) falsee)]
        | _ -> failwithf "too many clauses: %O" clauses
    | Assert _ as e -> failwithf "not impl: %O" e
    | CheckSat
    | DeclareDatatype _
    | DeclareSort _ as e -> [e]
    | _ -> __notImplemented__()

let to_clauses exprs =
    let typer = Typer()
    let to_relation = function
        | DefineFun(name, args, retType, body)
        | DefineFunRec(name, args, retType, body) ->
            typer.AddRelation(name, Relation(name, args, retType, body))
        | DeclareDatatype(_, constrs) ->
            constrs |> List.iter (typer.AddConstructor)
        | Assert _
        | CheckSat
        | DeclareSort _ -> ()
        | _ -> __notImplemented__()
    List.iter to_relation exprs
    List.collect (to_clause typer) exprs
    

let to_cvc4 exprs =
    let exprs = to_clauses exprs
    let sorted = exprs |> List.collect to_sorts
    let set_logic_all = List [Symbol "set-logic"; Symbol "ALL"]
    set_logic_all::sorted