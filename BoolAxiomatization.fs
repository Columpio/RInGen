module RInGen.BoolAxiomatization
open RInGen.SubstituteOperations
open IdentGenerator

type BoolAxiomatization () =
    inherit TheorySubstitutor ()
    let new_bool_sort = gensyms "Bool" |> PrimitiveSort

    let false_constr = gensyms "false"
    let true_constr = gensyms "true"
    let bool_datatype = DeclareDatatype(new_bool_sort, [false_constr, []; true_constr, []])
    let truet = TConst(true_constr, new_bool_sort)
    let falset = TConst(false_constr, new_bool_sort)


    let and_app, and_def, and_op = Relativization.createBinaryOperation "and" new_bool_sort new_bool_sort new_bool_sort
    let or_app, or_def, or_op = Relativization.createBinaryOperation "or" new_bool_sort new_bool_sort new_bool_sort
    let hence_app, hence_def, hence_op = Relativization.createBinaryOperation "hence" new_bool_sort new_bool_sort new_bool_sort
    let not_app, not_def, not_op = Relativization.createUnaryOperation "not" new_bool_sort new_bool_sort

    let toterm x = if x then truet else falset
    let symbolToTerm = function
        | s when s = "true" -> Some truet
        | s when s = "false" -> Some falset
        | _ -> None

    let generateDecl n app concreteFunction =
        let combinations = List.init n (fun _ -> [false; true]) |> List.product
        combinations |> List.map (fun combination -> rule [] [] <| app (List.map toterm combination) (toterm <| concreteFunction combination))

    let generateBinaryDecl app concreteFunction =
        let toBinary f = function [t1; t2] -> f t1 t2 | _ -> __unreachable__()
        generateDecl 2  (toBinary app) (toBinary concreteFunction)
    let generateUnaryDecl app concreteFunction =
        let toUnary f = function [t] -> f t | _ -> __unreachable__()
        generateDecl 1  (toUnary app) (toUnary concreteFunction)

    let and_decl = generateBinaryDecl and_app (&&)
    let or_decl = generateBinaryDecl or_app (||)
    let hence_decl = generateBinaryDecl hence_app (fun t1 t2 -> not t1 || t2)
    let not_decl = generateUnaryDecl not_app not

    let substitutions =
        [
            "and", and_op
            "or", or_op
            "not", not_op
            "=>", hence_op
        ] |> List.map (fun (name, op) -> Map.find (symbol name) elementaryOperations, (op, true)) |> Map.ofList

    let preamble =
        OriginalCommand bool_datatype
        :: List.map OriginalCommand [and_def; or_def; hence_def; not_def]
        @ List.map TransformedCommand (and_decl @ or_decl @ hence_decl @ not_decl)

    override x.MapReturnSortsFlag = false
    override x.GenerateDeclarations() = preamble, new_bool_sort, substitutions, symbolToTerm
    override x.TryMapSort(s) = if s = boolSort then Some new_bool_sort else None
