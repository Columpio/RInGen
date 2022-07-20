module RInGen.Context
open SMTLIB2

type Context() =
    inherit SMTLIB2.Context.Context()
    member x.Not =
        let notOperation op ts =
            match op, ts with
            | (Operations.NotT negop, ts) -> AApply(negop, ts) :: [] //TODO: approximates too much: see CHC-LIA-LIN-Arrays_001.smt2
            | (ElementaryOperation(testerName, [adtname], _) as mbTester, [arg]) ->
                match x.TryGetTesters adtname with
                | Some testers when List.contains mbTester testers ->
                    List.filter ((<>) mbTester) testers |> List.map (fun op -> Atom.apply1 op arg)
                | _ -> __notImplemented__()
        //    | AApply(UserDefinedOperation _, []) as e -> ANot e
        //    | AApply(UserDefinedOperation _, _) as e -> ANot e // TODO: failwithf "Trying to obtain negation of user defined predicate: %O" e
        //    | AAnd ts -> ts |> List.map nota |> AOr
        //    | AOr ts -> ts |> List.map nota |> AAnd
            | _ -> __notImplemented__()
        notMapApply notOperation List.singleton

    member x.AddToCTXTransformedCommand = function
        | OriginalCommand c -> x.AddToCTXCommand c
        | _ -> ()

    member x.LoadTransformedCommands = List.iter x.AddToCTXTransformedCommand