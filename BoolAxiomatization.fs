module RInGen.BoolAxiomatization
open RInGen.SubstituteOperations

let private and_app, and_def, and_op = Relativization.createBinaryOperation "and" boolSort boolSort boolSort
let private or_app, or_def, or_op = Relativization.createBinaryOperation "or" boolSort boolSort boolSort
let private hence_app, hence_def, hence_op = Relativization.createBinaryOperation "hence" boolSort boolSort boolSort
let private not_app, not_def, not_op = Relativization.createUnaryOperation "not" boolSort boolSort

let toterm x = if x then truet else falset

let private generateDecl n app concreteFunction =
    let combinations = List.init n (fun _ -> [false; true]) |> List.product
    combinations |> List.map (fun combination -> rule [] [] <| app (List.map toterm combination) (toterm <| concreteFunction combination))

let private generateBinaryDecl app concreteFunction =
    let toBinary f = function [t1; t2] -> f t1 t2 | _ -> __unreachable__()
    generateDecl 2  (toBinary app) (toBinary concreteFunction)
let private generateUnaryDecl app concreteFunction =
    let toUnary f = function [t] -> f t | _ -> __unreachable__()
    generateDecl 1  (toUnary app) (toUnary concreteFunction)

let private and_decl = generateBinaryDecl and_app (&&)
let private or_decl = generateBinaryDecl or_app (||)
let private hence_decl = generateBinaryDecl hence_app (fun t1 t2 -> not t1 || t2)
let private not_decl = generateUnaryDecl not_app not

let private substitutions =
    [
        "and", and_op
        "or", or_op
        "not", not_op
        "=>", hence_op
    ] |> List.map (fun (name, op) -> Map.find (symbol name) elementaryOperations, (op, true)) |> Map.ofList

let axiomatizeBoolOperations commands =
    let preamble =
        List.map OriginalCommand [and_def; or_def; hence_def; not_def]
        @ List.map TransformedCommand (and_decl @ or_decl @ hence_decl @ not_decl)
    let relativizer = SubstituteOperations(substitutions)
    let commands = List.map relativizer.SubstituteOperationsWithRelations commands
    if relativizer.WasSubstituted () then preamble @ commands else commands
