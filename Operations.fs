module RInGen.Operations

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

let emptyEqSubstitutor t1 t2 = Equal(t1, t2)
let emptyDiseqSubstitutor t1 t2 = Distinct(t1, t2)
let smartDiseqSubstitutor t1 t2 = emptyDiseqSubstitutor t1 t2
let private congruenceBySort empty opMap (sort : sort) =
    match Map.tryFind sort opMap with
    | Some op -> Atom.apply2 op
    | None -> empty
let equalBySort = congruenceBySort emptyEqSubstitutor
let disequalBySort = congruenceBySort emptyDiseqSubstitutor
let opSubstitutor empty opMap t1 t2 =
    let typ1 = Term.typeOf t1
    let typ2 = Term.typeOf t2
    if typ1 <> typ2
        then failwithf $"(Dis)equality of different sorts: {typ1} and {typ2}"
        else congruenceBySort empty opMap typ1 t1 t2


//let identToUserOp name sort = Operation.makeUserOperationFromSorts name [] sort

let operationToIdent = function
    | ElementaryOperation(name, _, sort)
    | UserDefinedOperation(name, _, sort) -> TIdent(name, sort)

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


let private negativeOperations =
    [
        "<=", ">"
        "<", ">="
        ">", "<="
        ">=", "<"
    ] |> List.map (fun (k, v) -> k, v) |> Map.ofList

let (|NotT|_|) = function
    | ElementaryOperation(name, _, _) ->
        opt {
            let! negname = Map.tryFind name negativeOperations
            return! Map.tryFind negname elementaryOperations
        }
    | _ -> None
