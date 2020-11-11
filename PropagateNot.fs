module FLispy.PropagateNot
open FLispy.Operations
open FLispy.Typer

let private generateDiseqHeader diseqs name =
    let diseq_name = gensymp ("diseq" + name)
    let op = ElementaryOperation(diseq_name, [name; name; "Bool"])
    let decl = DeclareFun(diseq_name, [name; name], "Bool")
    op, Map.add name op diseqs, decl

let private generateDiseqBody typer diseq_op diseqs cs sort =
    // Nat = Z | S Nat
    // diseqNat(Z, S y)
    // diseqNat(S x, Z)
    // diseqNat(x, y) -> diseqNat(S x, S y)
    // List = Nil | Cons(Nat, List)
    // diseqList(Nil, Cons(x, l))
    // diseqList(Cons(x, l), Nil)
    // diseqNat(x, y) -> diseqList(Cons(x, l1), Cons(y, l2))
    // diseqList(l1, l2) -> diseqList(Cons(x, l1), Cons(y, l2))
    let cs = cs |> List.map (fun (name, _) -> Map.find name typer)
    let diseq x y = Apply(diseq_op, [x; y])
    let apply op xs = if List.isEmpty xs then Ident(Operation.opName op, sort)  else Apply(op, xs)
    let facts = seq {
        for l, r in Seq.nondiag cs do
            let lvars = Operation.generateArguments l
            let rvars = Operation.generateArguments r
            let lids = lvars |> List.map Ident
            let rids = rvars |> List.map Ident
            yield Assert(forall (lvars @ rvars) (diseq (apply l lids) (apply r rids)))
    }
    let steps = seq {
        for constr in cs do
            let lvars = Operation.generateArguments constr
            let rvars = Operation.generateArguments constr
            let lids = lvars |> List.map Ident
            let rids = rvars |> List.map Ident
            let app = diseq (apply constr lids) (apply constr rids)
            for sort, l, r in List.zip3 (Operation.argumentTypes constr) lids rids do
                let diseq_op =
                    match Map.tryFind sort diseqs with
                    | Some op -> op
                    | None -> distinct_op
                yield Assert(forall (lvars @ rvars) (hence [Apply(diseq_op, [l; r])] app))
    }
    Seq.append facts steps |> List.ofSeq

let private generateTesterHeader sort constructorName =
    let testerName = "is-" + constructorName
    let op = ElementaryOperation(testerName, [sort; "Bool"])
    let decl = DeclareFun(testerName, [sort], "Bool")
    op, decl

let private generateTesterBody tester_op constructor_op =
    let constructorVars = Operation.generateArguments constructor_op
    Assert (forall constructorVars (Apply(tester_op, [Operation.makeAppConstructor constructor_op (List.map Ident constructorVars)])))

let private generateTesters typer sort cs =
    let generateTester (constructorName, _) =
        let op, decl = generateTesterHeader sort constructorName
        let body = generateTesterBody op (Map.find constructorName typer)
        [decl; body]
    cs |> List.collect generateTester

let propagateNot (typer, _) diseqs =
    let diseq = function
        | [x; _] as ts ->
            let tx = typeOf x
            match Map.tryFind tx diseqs with
            | Some op -> Apply(op, ts)
            | None -> Apply(distinct_op, ts)
        | ts -> failwithf "distinct with not 2 args: %O" ts
    let rec propNotExpr = function
        | Exists(vs, e) -> Exists(vs, propNotExpr e)
        | Forall(vs, e) -> Forall(vs, propNotExpr e)
        | Not e -> pushNot e
        | And es -> es |> List.map propNotExpr |> ande
        | Or es -> es |> List.map propNotExpr |> ore
        | Hence(t1, t2) -> Hence(propNotExpr t1, propNotExpr t2)
        | Apply(op, ts) ->
            let ts = List.map propNotExpr ts
            match ts with
            | [Not t1; Not t2] when op = distinct_op -> diseq [t1; t2]
            | [Not t1; t2]
            | [t1; Not t2] when op = distinct_op -> equal t1 t2
            | _ when op = distinct_op -> diseq ts
            | [Not t1; Not t2] when op = equal_op -> equal t1 t2
            | [Not t1; t2]
            | [t1; Not t2] when op = equal_op -> diseq [t1; t2]
            | _ -> Apply(op, ts)
        | Ite(i, t, e) -> Ite(propNotExpr i, propNotExpr t, propNotExpr e)
        | Let(asns, body) -> Let(List.map (fun (s, e) -> s, propNotExpr e) asns, propNotExpr body)
        | Match(t, cases) -> Match(propNotExpr t, List.map (fun (p, b) -> p, propNotExpr b) cases)
        | Constant _
        | Ident _ as e -> e
    and pushNot = function
        | Exists(vs, e) -> Forall(vs, pushNot e)
        | Forall(vs, e) -> Exists(vs, pushNot e)
        | Not e -> propNotExpr e
        | And es -> es |> List.map pushNot |> ore
        | Or es -> es |> List.map pushNot |> ande
        | Hence _ -> __unreachable__()
        | Apply(op, ts) ->
            let ts = List.map propNotExpr ts
            match ts with
            | [Not t1; Not t2] when op = distinct_op -> equal t1 t2
            | [Not t1; t2]
            | [t1; Not t2] when op = distinct_op -> diseq [t1; t2]
            | [t1; t2] when op = distinct_op -> equal t1 t2
            | [Not t1; Not t2] when op = equal_op -> diseq [t1; t2]
            | [Not t1; t2]
            | [t1; Not t2] when op = equal_op -> equal t1 t2
            | _ when op = equal_op -> diseq ts
            | _ -> Not <| Apply(op, ts)
        | Ite(i, t, e) -> Ite(propNotExpr i, pushNot t, pushNot e)
        | Let(asns, body) -> Let(List.map (fun (s, e) -> s, propNotExpr e) asns, pushNot body)
        | Match(t, cases) -> Match(propNotExpr t, List.map (fun (p, b) -> p, pushNot b) cases)
        | Constant(Bool b) -> Constant(Bool (not b))
        | Constant _
        | Ident _ as e -> Not e

    let propDefinition (name, argSorts, sort, body) = name, argSorts, sort, propNotExpr body

    function
    | DeclareConst _
    | GetInfo _
    | CheckSat
    | DeclareFun _
    | DeclareSort _
    | GetModel
    | SetLogic _ as c -> [c], diseqs
    | DeclareDatatype(name, cs) as c -> //TODO: selector
        let diseq_op, diseqs, diseq_decl = generateDiseqHeader diseqs name
        let body = generateDiseqBody typer diseq_op diseqs cs name
        let testers = generateTesters typer name cs
        c :: diseq_decl :: body @ testers, diseqs
    | DeclareDatatypes dts as c -> //TODO: selector
        let names, css = List.unzip dts
        let diseq_stuff, diseqs = List.mapFold (fun diseqs name -> let op, diseqs, decl = generateDiseqHeader diseqs name in (op, decl), diseqs) diseqs names
        let diseq_ops, diseq_decls = List.unzip diseq_stuff
        let diseq_bodies = List.map3 (fun name op cs -> generateDiseqBody typer op diseqs cs name) names diseq_ops css |> List.concat
        let testers = List.map2 (generateTesters typer) names css |> List.concat
        c :: diseq_decls @ diseq_bodies @ testers, diseqs
    | Assert e -> [Assert <| propNotExpr e], diseqs
    | DefineFun df -> [DefineFun <| propDefinition df], diseqs
    | DefineFunRec df -> [DefineFunRec <| propDefinition df], diseqs
    | DefineFunsRec dfs -> [dfs |> List.map propDefinition |> DefineFunsRec], diseqs

module private Bool =
    let private diseqName = gensymp "diseqBool"
    let diseqOp = ElementaryOperation(diseqName, ["Bool"; "Bool"; "Bool"])
    let diseqDeclaration =
        [
            DeclareFun(diseqName, ["Bool"; "Bool"], "Bool")
            Assert(Apply(diseqOp, [truee; falsee]))
            Assert(Apply(diseqOp, [falsee; truee]))
        ]

module Diseq =
    let empty = Map.ofList ["Bool", Bool.diseqOp]
    let preambula = Bool.diseqDeclaration

let private propagateAllNotsInBenchmark = typerFold propagateNot Diseq.empty >> List.concat

let propagateAllNots css = List.map propagateAllNotsInBenchmark css
