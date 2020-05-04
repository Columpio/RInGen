module FLispy.PropagateNot
open FLispy.Operations

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
                match Map.tryFind sort diseqs with
                | Some op -> yield Assert(forall (lvars @ rvars) (hence [Apply(op, [l; r])] app))
                | None -> failwithf "No diseq sort: %O" sort
    }
    Seq.append facts steps |> List.ofSeq

let propagateNot typer diseqs =
    let diseq = function
        | [x; _] as ts ->
            let tx = typeOf x
            Apply(Map.find tx diseqs, ts)
        | ts -> failwithf "distinct with not 2 args: %O" ts
    let rec propNotExpr = function
        | Exists(vs, e) -> Exists(vs, propNotExpr e)
        | Forall(vs, e) -> Forall(vs, propNotExpr e)
        | Not e -> pushNot e
        | And es -> es |> List.map propNotExpr |> And
        | Or es -> es |> List.map propNotExpr |> Or
        | Apply(op, ts) when op = distinct_op -> diseq ts
        | Ite(i, t, e) -> Ite(propNotExpr i, propNotExpr t, propNotExpr e)
        | Let(asns, body) -> Let(List.map (fun (s, e) -> s, propNotExpr e) asns, propNotExpr body)
        | Match(t, cases) -> Match(propNotExpr t, List.map (fun (p, b) -> p, propNotExpr b) cases)
        | Constant _
        | Ident _
        | Apply _ as e -> e
    and pushNot = function
        | Exists(vs, e) -> Forall(vs, pushNot e)
        | Forall(vs, e) -> Exists(vs, pushNot e)
        | Not e -> propNotExpr e
        | And es -> es |> List.map pushNot |> Or
        | Or es -> es |> List.map pushNot |> And
        | Apply(op, ts) when op = equal_op -> diseq ts
        | Ite(i, t, e) -> Ite(propNotExpr i, pushNot t, pushNot e)
        | Let(asns, body) -> Let(List.map (fun (s, e) -> s, propNotExpr e) asns, pushNot body)
        | Match(t, cases) -> Match(propNotExpr t, List.map (fun (p, b) -> p, pushNot b) cases)
        | Constant(Bool b) -> Constant(Bool (not b))
        | Constant _
        | Ident _
        | Apply _ as e -> Not e

    let propDefinition (name, argSorts, sort, body) = name, argSorts, sort, propNotExpr body

    function
    | DeclareConst _
    | GetInfo _
    | CheckSat
    | DeclareFun _
    | DeclareSort _
    | SetLogic _ as c -> [], c, diseqs
    | DeclareDatatype(name, cs) as c ->
        let diseq_op, diseqs, diseq_decl = generateDiseqHeader diseqs name
        let body = generateDiseqBody typer diseq_op diseqs cs name
        diseq_decl::body, c, diseqs
    | DeclareDatatypes dts as c ->
        let names, css = List.unzip dts
        let diseq_stuff, diseqs = List.mapFold (fun diseqs name -> let op, diseqs, decl = generateDiseqHeader diseqs name in (op, decl), diseqs) diseqs names
        let ops, decls = List.unzip diseq_stuff
        let diseq_bodies = List.map3 (fun name op cs -> generateDiseqBody typer op diseqs cs name) names ops css |> List.concat
        decls @ diseq_bodies, c, diseqs
    | Assert e -> [], Assert <| propNotExpr e, diseqs
    | DefineFun df -> [], DefineFun <| propDefinition df, diseqs
    | DefineFunRec df -> [], DefineFunRec <| propDefinition df, diseqs
    | DefineFunsRec dfs -> [], dfs |> List.map propDefinition |> DefineFunsRec, diseqs

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
