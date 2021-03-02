module RInGen.ParseToTerms
open RInGen.Operations

let private parseSort expr =
    let rec parseSort = function
        | PSymbol s -> s |> symbol |> PrimitiveSort
        | PList [PSymbol "Array"; indexSort; elementSort] -> ArraySort(parseSort indexSort, parseSort elementSort)
        | PList [PSymbol s] -> s |> symbol |> PrimitiveSort
        | _ -> __notImplemented__()
    parseSort expr

let private to_sorted_vars = List.map (function PList [PSymbol v; s] -> symbol v, parseSort s | _ -> __unreachable__())
let private to_var_binding = List.map (function PList [PSymbol v; t] -> symbol v, t | _ -> __unreachable__())

let rec private toExpr ((typer, env) as te) = function
    | PSymbol "true" -> BoolConst true
    | PSymbol "false" -> BoolConst false
    | PNumber n -> Number n
    | PList [PSymbol "forall"; PList vars; body] ->
        let vars = to_sorted_vars vars
        let te = VarEnv.replace te vars
        Forall(vars, toExpr te body)
    | PList [PSymbol "exists"; PList vars; body] ->
        let vars = to_sorted_vars vars
        let te = VarEnv.replace te vars
        Exists(vars, toExpr te body)
    | PList [PSymbol "let"; PList bindings; body] ->
        let handle_binding te (v, e) =
            let e = toExpr te e
            let s = Typer.typeOf e
            let vs = (v, s)
            let te = VarEnv.replaceOne te vs
            (vs, e), te
        let bindings = to_var_binding bindings
        let bindings, te = List.mapFold handle_binding te bindings
        let body = toExpr te body
        Let(bindings, body)
    | PList [PSymbol "ite"; i; t; e] -> Ite(toExpr te i, toExpr te t, toExpr te e)
    | PList (PSymbol op::args) ->
        match () with
        | _ when List.contains op ["and"; "or"; "not"; "=>"] ->
            let args = List.map (toExpr te) args
            match op, args with
            | "and", _ -> ande args
            | "or", _ -> ore args
            | "not", [arg] -> Not arg
            | "=>", [i; t] -> Hence(i, t)
            | e -> failwithf "%O" e
        | _ ->
            let args = List.map (toExpr te) args
            let oper = Typer.fillOperation typer (symbol op) (List.map Typer.typeOf args)
            match op, args with
            | "+", [Apply(ElementaryOperation("-", _, _) as minusOp, [t1]); t2] -> Apply(minusOp, [t2; t1]) // TODO: #parseWorkaround (+ (- a) b) = (- b a)
            | "<=", [t1; Apply(ElementaryOperation("-", _, _), [t2])] ->
                Apply(oper, [Apply(DummyOperations.addOp, [t1; t2]); Number 0L])// (<= a (- b)) = (<= (+ a b) 0)
            | _ -> Apply(oper, args)
    | PSymbol x -> let x = symbol x in Ident(x, VarEnv.typeGet x te)
    | PMatch(t, cases) ->
        let t = toExpr te t
        let typ = Typer.typeOf t
        let extendEnvironment ((typer, env) as te) = function
            | PSymbol v, typ ->
                let v = symbol v
                let vt = (v, typ)
                match Typer.tryTypeCheck v typer with
                | Some _ -> Ident vt, te
                | None ->
                    let te = VarEnv.replaceOne te vt
                    Ident vt, te
            | _ -> __unreachable__()
        let handle_case (pat, body) =
            match pat with
            | PList (PSymbol constr::cargs) ->
                let op = Typer.getOperation typer (symbol constr)
                let cargs, te = List.mapFold extendEnvironment te (List.zip cargs (Operation.argumentTypes op))
                Apply(op, cargs), toExpr te body
            | _ ->
                let v, te = extendEnvironment te (pat, typ)
                v, toExpr te body
        let cases = List.map handle_case cases
        Match(t, cases)
    | PList _ -> __unreachable__()
    | PComment -> __unreachable__()

let parseToTerms exprs =
    let toComm typer e =
        let define_fun name vars sort body constr =
            let vars = to_sorted_vars vars
            let typer = Typer.addOperation name (Operation.makeUserOperationFromVars name vars sort) typer
            let te = VarEnv.create typer vars
            let body = toExpr te body
            Definition(constr(name, vars, sort, body)), typer
        let parse_constructors typer adtname constrs =
            let handle_constr typer = function
                | PList (PSymbol fname::vars) ->
                    let fname = symbol fname
                    let vars = to_sorted_vars vars
                    let typer = List.fold (fun typer (pr, s) -> Typer.addOperation pr (Operation.makeElementaryOperationFromSorts pr [adtname] s) typer) typer vars
                    let typer = Typer.addOperation fname (Operation.makeElementaryOperationFromVars fname vars adtname) typer
                    let testerName = Symbols.addPrefix "is-" fname
                    let typer = Typer.addOperation testerName (Operation.makeElementaryOperationFromSorts testerName [adtname] boolSort) typer
                    (fname, vars), typer
                | _ -> __unreachable__()
            List.mapFold handle_constr typer constrs
        let comm, typer =
            match e with
            | PList [PSymbol "exit"] -> Command Exit, typer
            | PList [PSymbol "define-fun"; PSymbol name; PList vars; sort; body] ->
                define_fun (symbol name) vars (parseSort sort) body DefineFun
            | PList [PSymbol "define-fun-rec"; PSymbol name; PList vars; sort; body] ->
                define_fun (symbol name) vars (parseSort sort) body DefineFunRec
            | PList [PSymbol "define-funs-rec"; PList signs; PList bodies] ->
                let signs = signs |> List.map (function PList [PSymbol name; PList vars; sort] -> symbol name, to_sorted_vars vars, parseSort sort | _ -> __unreachable__())
                let typer = List.fold (fun typer (name, vars, sort) -> Typer.addOperation name (Operation.makeUserOperationFromVars name vars sort) typer) typer signs
                let fs = List.map2 (fun body (name, vars, sort) -> name, vars, sort, toExpr (VarEnv.create typer vars) body) bodies signs
                Definition <| DefineFunsRec fs, typer
            | PList [PSymbol "declare-datatype"; adtname; PList constrs] ->
                let adtname = parseSort adtname
                let constrs, typer = parse_constructors typer adtname constrs
                Command(DeclareDatatype(adtname, constrs)), typer
            | PList [PSymbol "declare-datatypes"; PList []; PList dfs] ->
                let parse typer = function
                    | PList (name :: constrs) ->
                        let name = parseSort name
                        let cs, typer = parse_constructors typer name constrs
                        (name, cs), typer
                    | _ -> __unreachable__()
                let dfs, typer = List.mapFold parse typer dfs
                Command(DeclareDatatypes dfs), typer
            | PList [PSymbol "declare-datatypes"; PList signs; PList constr_groups] ->
                let names = signs |> List.map (function PList [name; PNumber 0L] -> parseSort name | _ -> __unreachable__())
                let dfs, typer = List.mapFold (fun typer (name, PList constrs) -> parse_constructors typer name constrs) typer (List.zip names constr_groups)
                Command(DeclareDatatypes (List.zip names dfs)), typer
            | PList [PSymbol "check-sat"] -> Command <| CheckSat, typer
            | PList [PSymbol "get-model"] -> Command <| GetModel, typer
            | PList (PSymbol "get-info"::args) ->
                args |> List.map (function PSymbol option -> option | _ -> __notImplemented__()) |> join " " |> GetInfo |> Command, typer
            | PList [PSymbol "assert"; expr] ->
                Assert(toExpr (typer, VarEnv.empty) expr), typer
            | PList [PSymbol "declare-sort"; sort; PNumber 0L] -> DeclareSort(parseSort sort) |> Command, typer
            | PList [PSymbol "declare-sort"; sort] -> DeclareSort(parseSort sort) |> Command, typer
            | PList [PSymbol "declare-const"; PSymbol name; sort] ->
                let sort = parseSort sort
                let name = symbol name
                DeclareConst(name, sort) |> Command, Typer.addOperation name (Operation.makeUserOperationFromSorts name [] sort) typer
            | PList [PSymbol "declare-fun"; PSymbol name; PList argTypes; sort] ->
                let sort = parseSort sort
                let argTypes = argTypes |> List.map parseSort
                let name = symbol name
                DeclareFun(name, argTypes, sort) |> Command, Typer.addOperation name (Operation.makeUserOperationFromSorts name argTypes sort) typer
            | PList [PSymbol "set-logic"; PSymbol name] -> SetLogic(name) |> Command, typer
            | e -> failwithf "%O" e
        comm, typer
    let comms, _ = List.mapFold toComm Typer.empty exprs
    comms

let removeComments exprs =
    let rec removeComment = function
        | PComment -> None
        | PSymbol _
        | PNumber _ as e -> Some e
        | PList xs -> xs |> removeCommentsOne |> PList |> Some
        | PMatch(e, pats) ->
            opt {
                let! e = removeComment e
                let pats = removeCommentsTwo pats
                return PMatch(e, pats)
            }
    and removeCommentsOne = List.choose removeComment
    and removeCommentsTwo = List.choose (fun (x, y) -> Option.map2 pair (removeComment x) (removeComment y))
    removeCommentsOne exprs
