module SMTLIB2.Operations

let arithmeticOperations =
    let infix = true
    [
        ">", [IntSort; IntSort; BoolSort], (">", infix)
        "<", [IntSort; IntSort; BoolSort], ("<", infix)
        "<=", [IntSort; IntSort; BoolSort], ("=<", infix)
        ">=", [IntSort; IntSort; BoolSort], (">=", infix)
        "+", [IntSort; IntSort; IntSort], ("+", infix)
        "-", [IntSort; IntSort; IntSort], ("-", infix)
        "*", [IntSort; IntSort; IntSort], ("*", infix)
        "mod", [IntSort; IntSort; IntSort], ("mod", not infix)
        "div", [IntSort; IntSort; IntSort], ("div", not infix)
    ]

let elementaryOperations =
    let arithmeticOperations = List.map (fun (name, sorts, _) -> name, sorts) arithmeticOperations
    let ops = arithmeticOperations @ [
        "and", [BoolSort; BoolSort; BoolSort]
        "or", [BoolSort; BoolSort; BoolSort]
        "not", [BoolSort; BoolSort]
        "=>", [BoolSort; BoolSort; BoolSort]
    ]
    let ops = List.map (fun (op, sorts) -> op, Operation.makeElementaryOperationFromSorts op (List.initial sorts) (List.last sorts)) ops
    Map.ofList ops

module DummyOperations =
    let andOp = Map.find "and" elementaryOperations
    let orOp = Map.find "or" elementaryOperations
    let henceOp = Map.find "=>" elementaryOperations
    let notOp = Map.find "not" elementaryOperations
    let addOp = Map.find "+" elementaryOperations

let equal_op typ = Operation.makeElementaryRelationFromSorts "=" [typ; typ]
let distinct_op typ = Operation.makeElementaryRelationFromSorts "distinct" [typ; typ]

let private eqDiseqPattern = function
    | ElementaryOperation(name, [typ1; typ2], BoolSort) when typ1 = typ2 ->
        match name with
        | "=" -> Some true
        | "distinct" -> Some false
        | _ -> None
    | _ -> None
let (|Equality|_|) = eqDiseqPattern >> Option.bind (fun b -> if b then Some () else None)
let (|Disequality|_|) = eqDiseqPattern >> Option.bind (fun b -> if not b then Some () else None)

let findAndInstantiateGenericOperation opName argTypes =
    match opName, argTypes with
    | "select", [ArraySort(indexSort, itemSort) as arraySort; indexSort1] ->
        assert (indexSort1 = indexSort)
        Operation.makeElementaryOperationFromSorts "select" [arraySort; indexSort] itemSort
    | "store", [arraySort; _; _] ->
        Operation.makeElementaryOperationFromSorts "store" argTypes arraySort
    | "=", [typ1; typ2] when typ1 = typ2 -> equal_op typ1
    | "distinct", [typ1; typ2] when typ1 = typ2 -> distinct_op typ1
    | _ -> failwith $"No generic operation with name {opName} and sorts {argTypes}"
