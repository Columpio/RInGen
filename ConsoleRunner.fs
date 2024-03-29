﻿module RInGen.ConsoleRunner

open System
open RInGen.Programs
open RInGen.Transformers
open RInGen.Solvers
open SMTLIB2
open Argu
open System.IO

type TransformMode =
    | Original
    | FreeSorts
    | Prolog
    | TTATransform
    | [<Hidden>] RCHCTransform

type LocalTransformArguments =
    | [<Unique>] Tip
    | [<Unique>] Sync_terms

    interface IArgParserTemplate with
        member x.Usage =
            match x with
            | Tip -> "Negates the query (for TIP benchmarks)"
            | Sync_terms -> "Synchronize terms of a CHC system"

let private newTransformerProgram program mode transformOptions runSame =
    let transformOptions =
        match transformOptions with
        | Some (options : ParseResults<_>) ->
            {tip=options.Contains(Tip)
             sync_terms=options.Contains(Sync_terms)
             child_transformer=if options.Contains(Sync_terms) then Some(runSame transformOptions mode) else None}
        | None -> {tip=false; sync_terms=false; child_transformer=None}
    program(transformOptions) :> TransformerProgram, transformOptions
let private modeToTransformerProgram mode =
    match mode with
    | Original -> newTransformerProgram OriginalTransformerProgram
    | FreeSorts -> newTransformerProgram FreeSortsTransformerProgram
    | TTATransform -> newTransformerProgram TTATransformerProgram
    | Prolog -> newTransformerProgram PrologTransformerProgram
    | RCHCTransform -> newTransformerProgram RCHCTransformerProgram
    <| mode

type TransformArguments =
    | [<Unique; AltCommandLine("-m")>] Mode of TransformMode
    | [<Unique; Last; AltCommandLine("-t"); SubCommand>] Transform_options of ParseResults<LocalTransformArguments>
    | [<MainCommand; ExactlyOnce>] Path of PATH:path

    interface IArgParserTemplate with
        member x.Usage =
            match x with
            | Mode _ -> "Transformation mode: keep `original` smt2 declarations; transform ADTs to `free sorts` in smt2; transform to `Prolog` clauses (default: original)"
            | Transform_options _ -> "Apply additional transformations to the problem"
            | Path _ -> "Full path to file or directory"

let private print_transformation_success (path : RunConfig) = function
    | Some path' -> print_verbose $"Transformation run on %O{path} and the result is saved at %s{path'}"
    | None -> () // if the run was not successful, we have already printed the reason

let private transform outputPath runSame (options : ParseResults<TransformArguments>) =
    let transformOptions = options.TryGetResult(Transform_options)
    let path = options.GetResult(Path)
    let newTransformerProgram = modeToTransformerProgram <| options.GetResult(Mode, defaultValue = Original)
    let program, transformOptions = newTransformerProgram transformOptions runSame
    let path' = program.Run path outputPath
    if transformOptions.child_transformer.IsNone then
        if IN_VERBOSE_MODE () then print_transformation_success (PathRun path) path'
        elif IN_QUIET_MODE () then printfn $"""%s{Option.defaultValue "" path'}"""

type SolverName =
    | Z3
    | Eldarica
    | CVC_FMF
    | CVC_FMF_TTA
    | CVC_Ind
    | VeriMAP
    | Vampire
    | MyZ3
    | RCHC
//    | All

type SolveArguments =
    | [<Unique; Last; AltCommandLine("-t"); SubCommand>] Transform of ParseResults<LocalTransformArguments>
//    | [<Unique; AltCommandLine("-e")>] Keep_exist_quantifiers
    | [<Unique>] Table
    | [<ExactlyOnce; AltCommandLine("-s")>] Solver of SolverName
    | [<Unique>] In
    | [<Unique>] Path of PATH:path

    interface IArgParserTemplate with
        member x.Usage =
            match x with
//            | Keep_exist_quantifiers -> "Handle existential quantifiers (instead of sound halting with `unknown`)"
            | Solver _ -> "Run a specific solver"
            | In -> "Read from standard input"
            | Path _ -> "Read from file or directory from `PATH`"
            | Table -> "Generate .csv statistics table after solving"
            | Transform _ -> "Apply additional transformations to the problem (default: disabled; the solver is run on the original)"

let private solverByName = function
    | MyZ3 -> MyZ3Solver() :> SolverProgramRunner
    | Z3 -> Z3Solver() :> SolverProgramRunner
    | Eldarica -> EldaricaSolver() :> SolverProgramRunner
    | CVC_Ind -> CVC4IndSolver() :> SolverProgramRunner
    | VeriMAP -> VeriMAPiddtSolver() :> SolverProgramRunner
    | Vampire -> VampireSolver() :> SolverProgramRunner
    | CVC_FMF -> CVCFiniteSolver() :> SolverProgramRunner
    | RCHC -> RCHCSolver() :> SolverProgramRunner
    | CVC_FMF_TTA -> __unreachable__()
//    | All -> AllSolver() :> SolverProgramRunner

let private solverNameToTransformMode = function
    | MyZ3
    | Z3
    | Eldarica
    | CVC_Ind -> Original
    | VeriMAP -> Prolog
    | Vampire
    | CVC_FMF -> FreeSorts
    | RCHC -> RCHCTransform
    | CVC_FMF_TTA -> __unreachable__()

let private solve_interactive (solver : SolverProgramRunner) (transformer : TransformerProgram option) (outputPath : path option) =
    let tmpFileName =
        let tmpFileCounter = IdentGenerator.Counter()
        FileSystem.createTempFile {namer=Some(fun () -> $"iteration_{tmpFileCounter.Count()}"); extension=Some(solver.FileExtension); outputDir=outputPath}
    let transformer =
        match transformer with
        | Some transformer ->
            fun commands _ dstPath -> if transformer.PerformTransform InteractiveRun commands dstPath then Some dstPath else None
        | None -> fun _ srcPath _ -> Some srcPath
    let performTransformation commands =
        let dstPath = tmpFileName ()
        let srcPath = Path.ChangeExtension(dstPath, $".input%s{solver.FileExtension}")
        let lines = List.map toString commands
        Program.SaveFile srcPath lines
        transformer commands srcPath dstPath
    let runOn commands =
        opt {
            let! transformedPath = performTransformation commands
            let! path'' = solver.Run transformedPath outputPath
            print_verbose $"%s{solver.Name} run on %s{transformedPath} and the result is saved at %s{path''}"
            return ()
        } |> Option.defaultWith (fun () -> print_verbose "unknown")

    let parser = Parser.Parser()
    let prompt = if IN_QUIET_MODE () then fun () -> () else fun () -> printf "smt2> "
    let foldInputStream commands = function
        | Command CheckSat -> runOn (List.rev commands); commands
        | c -> c::commands
    seq {
        while true do
            prompt ()
            let line = Console.ReadLine()
            if line = null then () else
            eprint_extra_verbose $"received %d{line.Length}: %s{line}"
            let commands = parser.ParseLine(line)
            yield! commands
    }
    |> Seq.fold foldInputStream []
    |> ignore

let private printSolverSuccess name runPath resultPath =
    print_verbose $"{name} run on %s{runPath} and the result is saved at %s{resultPath}"

let private solve_from_path (solver : SolverProgramRunner) (transformer : TransformerProgram option) outputPath (options : ParseResults<SolveArguments>) path =
    let path' =
        let outputPath = Option.filter Directory.Exists outputPath
        match transformer with
        | Some transformer -> transformer.Run path outputPath
        | None -> Some path
    match path' with
    | None -> printfn "unknown" // no transformation, no solving
    | Some path' ->
    match solver.Run path' outputPath with
    | None -> printfn "unknown"
    | Some path'' ->
    printSolverSuccess solver.Name path' path''
    if not <| options.Contains(Table) then () else
    let table_path = solver.AddResultsToTable path path' path''
    print_verbose $"Saved run result at %s{table_path}"

let private runPortfolioSolver tipFlag origPath outputPath =
    let config = {tip=tipFlag; sync_terms=false; child_transformer=None}
    let transformations = [
        FreeSortsTransformerProgram(config) :> TransformerProgram, CVCFiniteSolver() :> SolverProgramRunner
        TTATransformerProgram(config), CVCFiniteSolver()
    ]
    let solver = PortfolioSolver(transformations)
    match solver.Run origPath outputPath with
    | None -> print_err_verbose $"Congiguration run halted with an error on portfolio on {origPath}"
    | Some targetPath -> printSolverSuccess CVC_FMF_TTA origPath targetPath

let private solve outputPath runSame (options : ParseResults<SolveArguments>) =
    let solver_name = options.GetResult(Solver)
    match solver_name with
    | CVC_FMF_TTA ->
        let tipFlag =
            match options.TryGetResult(Transform) with
            | Some (options : ParseResults<_>) -> options.Contains(Tip)
            | _ -> false
        runPortfolioSolver tipFlag (options.GetResult(Path)) outputPath
    | _ ->
    let transformer, opts =
        match options.TryGetResult(Transform) with
        | Some _ as transformOptions ->
            let mode = solverNameToTransformMode solver_name
            let t, opts = modeToTransformerProgram mode transformOptions runSame
            Some t, Some opts
        | None -> None, None
    let solver = solverByName solver_name
    match options.TryGetResult(Path) with
    | None ->
        match options.Contains(In) with
        | true -> solve_interactive solver transformer outputPath
        | false -> failwith $"Either `--in` or `--path` must be specified."
    | Some path -> solve_from_path solver transformer outputPath options path

[<RequireSubcommand>]
type CLIArguments =
    | [<Unique; AltCommandLine("-q")>] Quiet
    | [<Unique>] Timelimit of int
    | [<Unique; AltCommandLine("-o")>] Output_path of PATH:path
    | [<CliPrefix(CliPrefix.None); SubCommand>] Transform of ParseResults<TransformArguments>
    | [<CliPrefix(CliPrefix.None); SubCommand>] Solve of ParseResults<SolveArguments>

    interface IArgParserTemplate with
        member this.Usage =
            match this with
            | Transform _ -> "Transform SMTLIB2 file(s) into constrained Horn clauses"
            | Solve _ -> "Transform SMTLIB2 file(s) and run solver"
            | Quiet -> "Quiet mode"
            | Timelimit _ -> "Time limit, in seconds (default: 300)"
            | Output_path _ -> "Output path where to put new files (default: same as input PATH). Treated as a directory if ends with a directory separator (e.g., /). Otherwise, treated as file."

type SelfProgramRunner (parser : ArgumentParser<_>, generalArgs, transArgs : ParseResults<_> option, mode) =
    inherit ProgramRunner()
    let generalArgs = List.filter (function Transform _ | Solve _ | Output_path _ -> false | _ -> true) generalArgs
    let transArgs =
        match transArgs with
        | Some transArgs -> transArgs.GetAllResults()
        | None -> []
    let ltaParser = ArgumentParser.Create<LocalTransformArguments>()
    let transOpts = transArgs |> ltaParser.ToParseResults |> Transform_options
    let taParser = ArgumentParser.Create<TransformArguments>()
    let mutable currentDSTPath = ""

    member private x.RunSameConfiguration filename outputPath =
        let generalArgs = Output_path outputPath :: generalArgs
        let transformationArguments = [Mode mode; transOpts; TransformArguments.Path filename]
        let allArgs = generalArgs @ [transformationArguments |> taParser.ToParseResults |> Transform]
        parser.PrintCommandLineArgumentsFlat(allArgs)

    override x.ShouldSearchForBinaryInEnvironment = false
    override x.BinaryName = "/bin/bash"
    override x.BinaryOptions filename =
        let currentProcessVirtualMemKB = ThisProcess.thisProcess.VirtualMemorySize64 / (1L <<< 10)
        let desiredVirtualMemKB = MEMORY_LIMIT_MB * 1024L
        let childRun = $"dotnet %s{ThisProcess.thisDLLPath} %s{x.RunSameConfiguration filename currentDSTPath}".Replace("'", @"\'")
        let commands = [
            // set memory limit: see `man setrlimit`, `-v` for `RLIMIT_AS`, `-m` for `RLIMIT_RSS` (does not work)
            $"ulimit -v %d{currentProcessVirtualMemKB + desiredVirtualMemKB}"
            childRun
        ]
        $"""-c "%s{join "; " commands}" """

    override x.RunOnFile srcPath dstPath =
        currentDSTPath <- dstPath
        let statisticsFile, hasFinished, error, output = x.RunProcessOn srcPath
        if not <| IN_QUIET_MODE () then Printf.printfn_nonempty output
        Printf.eprintfn_nonempty error
        hasFinished && File.Exists(dstPath)

type ExitCodes =
    | Success = 0
    | Failure = -1

[<EntryPoint>]
let main args =
    let parser = ArgumentParser.Create<CLIArguments>(programName = "ringen")
    try
        let parseResults = parser.ParseCommandLine(inputs = args, raiseOnUsage = false).GetAllResults()
        if List.contains Quiet parseResults then VERBOSITY_MODE <- QUIET_MODE
        SECONDS_TIMEOUT <- List.tryPick (function Timelimit tl -> Some tl | _ -> None) parseResults |> Option.defaultValue SECONDS_TIMEOUT
        let outputPath = List.tryPick (function Output_path dir -> Some dir | _ -> None) parseResults
        let runSame transArgs mode = SelfProgramRunner(parser, parseResults, transArgs, mode) :> ProgramRunner
        match List.find (function Transform _ | Solve _ -> true | _ -> false) parseResults with
        | Transform args -> transform outputPath runSame args
        | Solve args -> solve outputPath runSame args
        | _ -> __unreachable__()
        int ExitCodes.Success
    with :? ArguParseException as e ->
        printfn $"{e.Message}"
        int ExitCodes.Failure
