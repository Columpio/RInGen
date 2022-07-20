module RInGen.Operations
open SMTLIB2

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

let operationToIdent = function
    | ElementaryOperation(name, _, sort)
    | UserDefinedOperation(name, _, sort) -> TIdent(name, sort)

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
            return! Map.tryFind negname Operations.elementaryOperations
        }
    | _ -> None
