module RInGen.FiniteModels
open Antlr4.Runtime
open RInGen.SMTExpr

type finModel =
    | SomeFiniteModel
    | ConcreteFiniteModel of (symbol * int) list * definition list // (sort * cardinality) list * model

let parseCVC modelLines =
    let p = Parser()
    let sorts, model = p.ParseModel(modelLines)
    ConcreteFiniteModel(sorts, model)
