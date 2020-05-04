module FLispy.Operations
open System.Collections.Generic

let gensymp =
    let symbols = Dictionary<string, int>()
    fun prefix ->
        let counter = ref 0
        if symbols.TryGetValue(prefix, counter) then
            symbols.[prefix] <- !counter + 1
        else
            symbols.Add(prefix, 1)
        sprintf "%s@%d" prefix !counter

let gensym () = gensymp "x"

module Operation =
    let private getSortOfOperation = function
        | ElementaryOperation(_, s)
        | UserDefinedOperation(_, s) -> s
    let opName = function
        | ElementaryOperation(n, _)
        | UserDefinedOperation(n, _) -> n
    let argumentTypes = getSortOfOperation >> List.tail

    let private returnTypeOfSignature = List.head
    let returnType = getSortOfOperation >> returnTypeOfSignature

    let makeOperationSortsFromTypes sorts retSort = retSort :: sorts
    let makeOperationSortsFromVars vars retSort = makeOperationSortsFromTypes (List.map snd vars) retSort
    let makeUserOperationFromVars name vars retSort = UserDefinedOperation(name, makeOperationSortsFromVars vars retSort)
    let makeUserOperationFromSorts name argSorts retSort = UserDefinedOperation(name, makeOperationSortsFromTypes argSorts retSort)
    let makeElementaryOperationFromVars name vars retSort = ElementaryOperation(name, makeOperationSortsFromVars vars retSort)
    let makeElementaryOperationFromSorts name argSorts retSort = ElementaryOperation(name, makeOperationSortsFromTypes argSorts retSort)

    let makeApp op args ret = Apply(op, makeOperationSortsFromTypes args ret)

    let generateReturnArgument sign =
        let retType = returnTypeOfSignature sign
        let retArg = gensym (), retType
        let retVar = Ident retArg
        retArg, retVar

    let generateArguments = argumentTypes >> List.map (fun s -> gensym(), s)


let elementaryOperations =
    let ops = [
        "=", ["*dummy-type*"; "*dummy-type*"; "Bool"]
        "distinct", ["*dummy-type*"; "*dummy-type*"; "Bool"]
        ">", ["Int"; "Int"; "Bool"]
        "<", ["Int"; "Int"; "Bool"]
        "<=", ["Int"; "Int"; "Bool"]
        ">=", ["Int"; "Int"; "Bool"]
        "+", ["Int"; "Int"; "Int"]
        "-", ["Int"; "Int"; "Int"]
        "*", ["Int"; "Int"; "Int"]
        "mod", ["Int"; "Int"; "Int"]
        "div", ["Int"; "Int"; "Int"]
        "=>", ["Bool"; "Bool"; "Bool"]
    ]
    let ops = List.map (fun ((op, _) as os) -> op, ElementaryOperation(os)) ops
    Map.ofList ops
let distinct_op = Map.find "distinct" elementaryOperations
let equal_op = Map.find "=" elementaryOperations

let hence =
    let f = Map.find "=>" elementaryOperations
    fun ts t ->
        match ts with
        | [] -> t
        | [ts] -> Apply(f, [ts; t])
        | _ -> Apply(f, [And ts; t])
let equal t1 t2 = Apply(equal_op, [t1; t2])
let forall vars e = if List.isEmpty vars then e else Forall(vars, e)

let rec typeOf = function
    | Constant(Number _) -> "Int"
    | Forall _
    | Exists _
    | And _
    | Or _
    | Not _
    | Constant(Bool _) -> "Bool"
    | Ident(_, t) -> t
    | Apply(op, _) -> Operation.returnType op
    | Match(_, ((_, t)::_))
    | Ite(_, t, _)
    | Let(_, t) -> typeOf t
    | Match(_, []) -> __unreachable__()
