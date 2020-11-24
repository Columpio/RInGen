module RInGen.ADTExtensions

open RInGen.Typer

let getFreeVarsFromPattern (typer : Typer) =
    let rec get_free_vars = function
        | Apply(_, ts) -> List.collect get_free_vars ts
        | Ident(name, _) when typer.containsKey name -> []
        | Ident(v, t) -> [v, t]
        | _ -> __unreachable__()
    get_free_vars

let rec isUnifiableWith typer p1 p2 =
    match p1, p2 with
    | Apply(op1, ts1), Apply(op2, ts2) -> op1 = op2 && List.forall2 (isUnifiableWith typer) ts1 ts2
    | Ident(name1, _), _ when not <| Map.containsKey name1 typer -> true
    | _, Ident(name2, _) when not <| Map.containsKey name2 typer -> true
    | Ident(name1, sort1), Ident(name2, sort2) -> name1 = name2 && sort1 = sort2
    | _ -> false

let patternsToConstraints (typer : Typer) usedPatterns currentPattern patternMatch =
    let getHead = function
        | Ident(name, _)
        | Apply(ElementaryOperation(name, _, _), _) when typer.containsKey name -> Some name
        | _ -> None
    let makePatternMatchWithOp opName =
        let op = typer.find opName
        let args = IdentGenerator.generateArguments op
        args, patternMatch (Apply(op, List.map Ident args))
    match currentPattern with
    | Ident(name, sort) when not <| typer.containsKey name -> // placeholder case
        let heads = List.choose getHead usedPatterns
        let allConstructorNames = typer.getConstructors sort
        let rest = Set.difference (Set.ofList allConstructorNames) (Set.ofList heads) |> Set.toList
        List.map makePatternMatchWithOp rest
    | _ -> [[], patternMatch currentPattern]
