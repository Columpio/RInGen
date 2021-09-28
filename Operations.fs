[<AutoOpen>]
module RInGen.Operations

module Operation =
    let argumentTypes = function
        | ElementaryOperation(_, s, _)
        | UserDefinedOperation(_, s, _) -> s
    let returnType = function
        | ElementaryOperation(_, _, s)
        | UserDefinedOperation(_, _, s) -> s
    let opName = function
        | ElementaryOperation(n, _, _)
        | UserDefinedOperation(n, _, _) -> n

    let changeName name = function
        | ElementaryOperation(_, s1, s2) -> ElementaryOperation(symbol name, s1, s2)
        | UserDefinedOperation(_, s1, s2) -> UserDefinedOperation(symbol name, s1, s2)

    let flipOperationKind = function
        | UserDefinedOperation(n, s1, s2) -> ElementaryOperation(n, s1, s2)
        | ElementaryOperation(n, s1, s2) -> UserDefinedOperation(n, s1, s2)

    let makeUserOperationFromVars name vars retSort = UserDefinedOperation(name, List.map snd vars, retSort)
    let makeUserOperationFromSorts name argSorts retSort = UserDefinedOperation(name, argSorts, retSort)
    let makeUserRelationFromVars name vars = makeUserOperationFromVars name vars boolSort
    let makeElementaryOperationFromVars name vars retSort = ElementaryOperation(name, List.map snd vars, retSort)
    let makeElementaryOperationFromSorts name argSorts retSort = ElementaryOperation(name, argSorts, retSort)
    let makeElementaryRelationFromVars name vars = makeElementaryOperationFromVars name vars boolSort
    let makeElementaryRelationFromSorts name argSorts = makeElementaryOperationFromSorts name argSorts boolSort

    let declareOp = function
        | ElementaryOperation(name, argSorts, retSort) -> DeclareFun(name, argSorts, retSort)
        | UserDefinedOperation(name, argSorts, retSort) -> DeclareFun(name, argSorts, retSort)

    let private operationToIdent = function
        | UserDefinedOperation(name, [], ret) -> Ident(name, ret)
        | ElementaryOperation(name, [], ret) -> Ident(name, ret)
        | op -> failwithf $"Can't create identifier from operation: {op}"

    let generateReturnArgument op =
        let retType = returnType op
        let retArg = IdentGenerator.gensym (), retType
        let retVar = TIdent retArg
        retArg, retVar

    let generateArguments = argumentTypes >> List.map (fun s -> IdentGenerator.gensym (), s)

let arithmeticOperations =
    let infix = true
    [
        ">", [integerSort; integerSort; boolSort], (">", infix)
        "<", [integerSort; integerSort; boolSort], ("<", infix)
        "<=", [integerSort; integerSort; boolSort], ("=<", infix)
        ">=", [integerSort; integerSort; boolSort], (">=", infix)
        "+", [integerSort; integerSort; integerSort], ("+", infix)
        "-", [integerSort; integerSort; integerSort], ("-", infix)
        "*", [integerSort; integerSort; integerSort], ("*", infix)
        "mod", [integerSort; integerSort; integerSort], ("mod", not infix)
        "div", [integerSort; integerSort; integerSort], ("div", not infix)
    ]

let elementaryOperations =
    let arithmeticOperations = List.map (fun (name, sorts, _) -> name, sorts) arithmeticOperations
    let ops = arithmeticOperations @ [
        "=", [dummySort; dummySort; boolSort]
        "distinct", [dummySort; dummySort; boolSort]
        "and", [boolSort; boolSort; boolSort]
        "or", [boolSort; boolSort; boolSort]
        "not", [boolSort; boolSort]
        "=>", [boolSort; boolSort; boolSort]
        "store", [ArraySort(dummySort, dummySort); dummySort; dummySort; ArraySort(dummySort, dummySort)]
        "select", [ArraySort(dummySort, dummySort); dummySort; dummySort]
    ]
    let ops = List.map (fun (op, sorts) -> (symbol op), Operation.makeElementaryOperationFromSorts (symbol op) (List.initial sorts) (List.last sorts)) ops
    Map.ofList ops

let integerPredicates = ["="; "distinct"; "<"; "<="; ">"; ">="]

module DummyOperations =
    let andOp = Map.find "and" elementaryOperations
    let orOp = Map.find "or" elementaryOperations
    let henceOp = Map.find "=>" elementaryOperations
    let notOp = Map.find "not" elementaryOperations
    let addOp = Map.find "+" elementaryOperations

let equal_op typ = Operation.makeElementaryRelationFromSorts (symbol "=") [typ; typ]
let distinct_op typ = Operation.makeElementaryRelationFromSorts (symbol "distinct") [typ; typ]
let smartDiseqSubstitutor t1 t2 = distinct t1 t2
let emptyEqSubstitutor t1 t2 = Equal(t1, t2)
let emptyDiseqSubstitutor t1 t2 = Distinct(t1, t2)
let applyBinaryRelation op x y = AApply(op, [x; y])
let private congruenceBySort empty opMap (sort : sort) =
    match Map.tryFind sort opMap with
    | Some op -> applyBinaryRelation op
    | None -> empty
let equalBySort = congruenceBySort emptyEqSubstitutor
let disequalBySort = congruenceBySort emptyDiseqSubstitutor
let opSubstitutor empty opMap t1 t2 =
    let typ1 = Term.typeOf t1
    let typ2 = Term.typeOf t2
    if typ1 <> typ2
        then failwithf $"(Dis)equality of different sorts: {typ1} and {typ2}"
        else congruenceBySort empty opMap typ1 t1 t2


let identToUserOp name sort = Operation.makeUserOperationFromSorts name [] sort
let userOpToIdent = function
    | UserDefinedOperation(name, [], sort) -> TIdent(name, sort)
    | op -> failwithf $"Can't create identifier from operation: {op}"

let selectFromArraySort arraySort =
    let indexSort, itemSort = Sort.argumentSortsOfArraySort arraySort
    Operation.makeElementaryOperationFromSorts (symbol "select") [arraySort; indexSort] itemSort

let fillDummyOperationTypes op argTypes =
    match op, argTypes with
    | ElementaryOperation("select", _, _), [arraySort; _] -> selectFromArraySort arraySort
    | ElementaryOperation("store", _, _), [arraySort; _; _] ->
        Operation.makeElementaryOperationFromSorts ("store") argTypes arraySort
    | ElementaryOperation("=", _, _), [typ; _] -> equal_op typ
    | ElementaryOperation("distinct", _, _), [typ; _] -> distinct_op typ
    | _ -> op


let private negativeOperations =
    [
        "<=", ">"
        "<", ">="
        ">", "<="
        ">=", "<"
    ] |> List.map (fun (k, v) -> symbol k, symbol v) |> Map.ofList

let (|NotT|_|) = function
    | ElementaryOperation(name, _, _) ->
        opt {
            let! negname = Map.tryFind name negativeOperations
            return! Map.tryFind negname elementaryOperations
        }
    | _ -> None
