module RInGen.FiniteModels
open Antlr4.Runtime
open RInGen.SMTExpr

type finModel =
    | SomeFiniteModel
    | ConcreteFiniteModel of (symbol * symbol list) list * definition list // (sort * cardinality) list * model
    override x.ToString() =
        match x with
        | SomeFiniteModel -> "SomeFiniteModel"
        | ConcreteFiniteModel(sorts, defs) ->
            let sortLines = sorts |> List.map (fun (s, reps) -> $"""; {s} = {{{reps |> List.map toString |> List.sort |> join ", "}}}""")
            let defLines = List.map toString defs
            Environment.join (sortLines @ defLines)

let parseCVC modelLines =
    let p = Parser()
    let sorts, model = p.ParseModel(modelLines)
    ConcreteFiniteModel(sorts, model)
