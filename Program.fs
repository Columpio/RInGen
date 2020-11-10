module FLispy.Program

open FLispy.Solvers
open CommandLine


type options = {
    [<Option("sorts", HelpText = "Convert ADTs to sorts (preprocessing for the finite-model finder)")>] tosorts : bool
    [<Option("tipToHorn", HelpText = "Convert TIP like systems to Horn clauses")>] tipToHorn : bool
    [<Option('d', "directory", HelpText = "Run on directory")>] directory : string option
    [<Option('f', "file", HelpText = "Run on single file")>] filename : string option
    [<Option('s', "solve", HelpText = "Solve with the finite-model finder after preprocessing (requires --sorts)")>] solve : bool
}

[<EntryPoint>]
let main args =
    let result = Parser.Default.ParseArguments<options>(args)
    match result with
    | :? Parsed<options> as parsed ->
        let cvc4 = CVC4FiniteSolver()
        match parsed.Value with
        | {tosorts=_; tipToHorn=_; directory=Some _; filename=Some _; solve=_}
        | {tosorts=_; tipToHorn=_; directory=None; filename=None; solve=_} ->
            failwith "Should specify either --directory or --file to be preprocessed"
        | {tosorts=tosorts; tipToHorn=tipToHorn; directory=Some directory; filename=None; solve=solve} when not solve || tosorts ->
            let outputDirectory = (if tosorts then cvc4.GenerateClauses else Z3Solver().GenerateClauses) tipToHorn (not tipToHorn) directory
            printfn "CHC systems of directory %s are preprocessed and saved in %s" directory outputDirectory
            if solve then
                let resultsDirectory = cvc4.RunOnBenchmarkSet true outputDirectory
                printfn "Solver run on %s and saved results in %s" outputDirectory resultsDirectory
        | {tosorts=tosorts; tipToHorn=tipToHorn; directory=None; filename=Some filename; solve=solve} when not solve || tosorts ->
            let outputFiles = (if tosorts then cvc4.GenerateClausesSingle else Z3Solver().GenerateClausesSingle) tipToHorn filename
            match outputFiles with
            | [outputFile] ->
                printfn "CHC system in %s is preprocessed and saved in %s" filename outputFile
                if solve then
                    let result, time = cvc4.SolveWithTime outputFile
                    printfn "Solver run on %s and the result is %O which was obtained in %d msec." outputFile result time
            | _ ->
                printfn "Preprocessing of %s produced %d files:" filename (List.length outputFiles)
                List.iter (printfn "%s") outputFiles
                if solve then
                    for outputFile in outputFiles do
                        let result, time = cvc4.SolveWithTime outputFile
                        printfn "Solver run on %s and the result is %O which was obtained in %d msec." outputFile result time
        | _ -> failwith "--sorts is required with --solve"
    | :? NotParsed<options> as notParsed -> failwithf "Parsing errors: %O" notParsed.Errors
    | _ -> failwith "Fail during argument parsing"
    0

//let main args =
//    let tip = "/home/columpio/Desktop/benchmarks/TIP", false
//    let reynolds = "/home/columpio/Desktop/benchmarks/Reynolds"
//    let reynolds_tr = "/home/columpio/Desktop/benchmarks/Reynolds-transformed"
//    let positiveEq = "/home/columpio/Desktop/benchmarks/PositiveEq", true
//    let diseq = "/home/columpio/Desktop/benchmarks/Diseq", true
////    if true then
//    if false then
////        CVC4IndSolver().EncodeSingleFile("/home/columpio/Desktop/benchmarks/PositiveEq/goal76.smt2") |> List.iter (printfn "%O")
//        let baseTIP = "/home/columpio/Desktop/benchmarks/TIP"
//        ResultTable.GenerateLaTeXResultTable [baseTIP + ".CVC4Finite.CVC4FiniteAnswers"; baseTIP + ".Eldarica.EldaricaAnswers"; baseTIP + ".Z3.Z3Answers"; baseTIP + ".CVC4Ind.CVC4IndAnswers"]
////        ResultTable.GenerateReadableResultTable [baseTIP + ".CVC4Finite.CVC4FiniteAnswers"; baseTIP + ".Eldarica.EldaricaAnswers"; baseTIP + ".Z3.Z3Answers"; baseTIP + ".CVC4Ind.CVC4IndAnswers"]
//    else
//        // A /\ E x. p(x) <-> E x. (A /\ p(x))
//        // !A -> E x. p(x) <-> E x. (!A -> p(x))
////        let tool = CVC4FiniteSolver()
////        let tool = EldaricaSolver()
//        let overwrite = false
//        let tools : ISolver list = [CVC4FiniteSolver(); Z3Solver()]
//        for tool in tools do
//            for dirname, force in [tip] do //; reynolds; reynolds_tr] do
//                let dir = tool.GenerateClauses force dirname
//                dir |> ignore
////                tool.RunOnBenchmarkSet overwrite dir |> ignore
//    0
