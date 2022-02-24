module RInGen.Relativization
open Operations

let private relative args ret = ret :: args
let private returnSort = List.head
let private argumentSorts = List.tail

let createRelativeOperation constr name args ret = constr(name, relative args ret, BoolSort)

let relativizeOperation = function
    | UserDefinedOperation(name, args, ret) -> createRelativeOperation UserDefinedOperation name args ret
    | ElementaryOperation(name, args, ret) -> createRelativeOperation ElementaryOperation name args ret

let derelativizeOperation = function
    | UserDefinedOperation(name, args, ret) when ret = BoolSort -> UserDefinedOperation(name, argumentSorts args, returnSort args)
    | ElementaryOperation(name, args, ret) when ret = BoolSort -> ElementaryOperation(name, argumentSorts args, returnSort args)
    | _ -> __unreachable__()

let relapply op args res = AApply(op, relative args res)
let reldeclare name args res = DeclareFun(name, relative args res, BoolSort)

let addShouldRelativize name op = Map.add name (op, true)
let addShouldNotRelativize name op = Map.add name (op, false)

let createNAryRelation name sorts =
    let name = IdentGenerator.gensymp name
    let op = Operation.makeElementaryRelationFromSorts name sorts
    let decl = DeclareFun(name, sorts, BoolSort)
    decl, op

let createBinaryRelation name sort1 sort2 =
    let decl, op = createNAryRelation name [sort1; sort2]
    let app x y = AApply(op, [x; y])
    app, decl, op

let createUnaryRelation name sort =
    let decl, op = createNAryRelation name [sort]
    let app x = AApply(op, [x])
    app, decl, op

let createNAryOperation name sorts retSort =
    let name = IdentGenerator.gensymp name
    let op = createRelativeOperation ElementaryOperation name sorts retSort
    let decl = reldeclare name sorts retSort
    decl, op

let createBinaryOperation name sort1 sort2 retSort =
    let decl, op = createNAryOperation name [sort1; sort2] retSort
    let app x y r = relapply op [x; y] r
    app, decl, op

let createUnaryOperation name sort retSort =
    let decl, op = createNAryOperation name [sort] retSort
    let app x r = relapply op [x] r
    app, decl, op
