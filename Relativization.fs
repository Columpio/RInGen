module RInGen.Relativization
open Operations

let private relative args ret = ret :: args
let private returnSort = List.head
let private argumentSorts = List.tail

let createRelativeOperation constr name args ret = constr(name, relative args ret, boolSort)

let relativizeOperation = function
    | UserDefinedOperation(name, args, ret) -> createRelativeOperation UserDefinedOperation name args ret
    | ElementaryOperation(name, args, ret) -> createRelativeOperation ElementaryOperation name args ret

let derelativizeOperation = function
    | UserDefinedOperation(name, args, ret) when ret = boolSort -> UserDefinedOperation(name, argumentSorts args, returnSort args)
    | ElementaryOperation(name, args, ret) when ret = boolSort -> ElementaryOperation(name, argumentSorts args, returnSort args)
    | _ -> __unreachable__()

let relapply op args res = AApply(op, relative args res)
let reldeclare name args res = DeclareFun(name, relative args res, boolSort)

let addShouldRelativize name op = Map.add name (op, true)
let addShouldNotRelativize name op = Map.add name (op, false)

let operationsOfADT ((adtname, cs) : symbol * (symbol * sorted_var list) list) =
    let handle_constr (constructorName, vars) =
        let selectors = List.map (fun (pr, s) -> (Operation.makeElementaryOperationFromSorts pr [PrimitiveSort adtname] s)) vars
        selectors
    List.collect handle_constr cs