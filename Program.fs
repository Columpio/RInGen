module FLispy.Program

open FLispy.Solvers
open CommandLine

type options = {
    [<Option("sorts", HelpText = "Convert ADTs to sorts (preprocessing for the finite-model finder)")>] tosorts : bool
    [<Option("tipToHorn", HelpText = "Convert TIP like systems to Horn clauses")>] tipToHorn : bool
    [<Option('d', "directory", HelpText = "Run on directory")>] directory : string option
    [<Option('f', "file", HelpText = "Run on single file")>] filename : string option
    [<Option('s', "solver", HelpText = "Run a specific solver (one of: z3 | eldarica | cvc4f | cvc4ind | all) after processing")>] solver : string option
    [<Option('t', "timelimit", HelpText = "Time limit, in seconds (default 300)")>] timelimit : int option
}

let solverByName (solverName : string) tosorts =
    let solverName = solverName.ToLower()
    match tosorts with
    | false when solverName = "z3" -> Z3Solver() :> ISolver
    | false when solverName = "eldarica" -> EldaricaSolver() :> ISolver
    | false when solverName = "cvc4ind" -> CVC4IndSolver() :> ISolver
    | true when solverName = "cvc4f" -> CVC4FiniteSolver() :> ISolver
    | _ when solverName = "all" -> AllSolver() :> ISolver
    | _ when List.contains solverName ["z3"; "eldarica"; "cvc4f"; "cvc4ind"; "all"] -> failwithf "Invalid combination of --sorts and --solver flags."
    | _ -> failwithf "Unknown solver: %s. Specify one of: z3, eldarica, cvc4f, cvc4ind." solverName

let solverOrPreprocessor solverName tosorts =
    match solverName, tosorts with
    | Some solverName, _ -> solverByName solverName tosorts
    | None, true -> CVC4FiniteSolver() :> ISolver
    | None, false -> Z3Solver() :> ISolver

[<EntryPoint>]
let main args =
    let result = Parser.Default.ParseArguments<options>(args)
    match result with
    | :? Parsed<options> as parsed ->
        match parsed.Value.timelimit with
        | Some timelimit -> SolverResult.SECONDS_TIMEOUT <- timelimit
        | None -> ()
        match parsed.Value with
        | {tosorts=_; tipToHorn=_; directory=Some _; filename=Some _; solver=_; timelimit=_}
        | {tosorts=_; tipToHorn=_; directory=None; filename=None; solver=_; timelimit=_} ->
            failwith "Should specify either --directory or --file"
        | {tosorts=tosorts; tipToHorn=tipToHorn; directory=Some directory; filename=None; solver=solverName; timelimit=_} ->
            let solver = solverOrPreprocessor solverName tosorts
            let outputDirectory = solver.GenerateClauses tipToHorn (not tipToHorn) directory
            printfn "CHC systems of directory %s are preprocessed and saved in %s" directory outputDirectory
            if Option.isSome solverName then
                let resultsDirectory = solver.RunOnBenchmarkSet false outputDirectory
                printfn "Solver run on %s and saved results in %s" outputDirectory resultsDirectory
        | {tosorts=tosorts; tipToHorn=tipToHorn; directory=None; filename=Some filename; solver=solverName; timelimit=_} ->
            let solver = solverOrPreprocessor solverName tosorts
            let outputFiles = solver.GenerateClausesSingle tipToHorn filename
            match outputFiles with
            | [outputFile] ->
                printfn "CHC system in %s is preprocessed and saved in %s" filename outputFile
                if Option.isSome solverName then
                    let result, time = solver.SolveWithTime outputFile
                    printfn "Solver run on %s and the result is %O which was obtained in %d msec." outputFile result time
            | _ ->
                printfn "Preprocessing of %s produced %d files:" filename (List.length outputFiles)
                List.iter (printfn "%s") outputFiles
                if Option.isSome solverName then
                    for outputFile in outputFiles do
                        let result, time = solver.SolveWithTime outputFile
                        printfn "Solver run on %s and the result is %O which was obtained in %d msec." outputFile result time
    | :? NotParsed<options> -> ()
    | _ -> failwith "Fail during argument parsing"
    0
