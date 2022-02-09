module RInGen.Main

open System
open RInGen.Programs
open RInGen.Transformers
open RInGen.Solvers
open Argu
open System.IO

type TransformMode =
    | Original
    | FreeSorts
    | Prolog
    | [<Hidden>] RCHCTransform

type LocalTransformArguments =
    | [<Unique; Hidden>] No_Isolation
    | [<Unique>] Tip
    | [<Unique>] Sync_terms
    | [<Unique>] Tta_transform

    interface IArgParserTemplate with
        member x.Usage =
            match x with
            | No_Isolation -> "Perform transformation without monitoring"
            | Tip -> "Negates the query (for TIP benchmarks)"
            | Sync_terms -> "Synchronize terms of a CHC system"
            | Tta_transform -> "Apply transformation for tuple tree automata inference"

let private newTransformerProgram program mode transformOptions runSame =
    let transformOptions =
        match transformOptions with
        | Some (options : ParseResults<_>) ->
            {tip=options.Contains(Tip)
             sync_terms=options.Contains(Sync_terms)
             tta_transform=options.Contains(Tta_transform)
             child_transformer=if options.Contains(No_Isolation) then None else Some(runSame transformOptions mode)}
        | None -> {tip=false; sync_terms=false; tta_transform=false; child_transformer=None}
    program(transformOptions) :> TransformerProgram, transformOptions
let private modeToTransformerProgram mode =
    match mode with
    | Original -> newTransformerProgram OriginalTransformerProgram
    | FreeSorts -> newTransformerProgram FreeSortsTransformerProgram
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
    | CVC_FMF -> CVC4FiniteSolver() :> SolverProgramRunner
    | RCHC -> RCHCSolver() :> SolverProgramRunner
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

let private solve_interactive (solver : SolverProgramRunner) (transformer : TransformerProgram option) (outputPath : path option) =
    let tmpFileCounter = IdentGenerator.Counter()
    let tmpFileName () = Path.Combine(Path.GetTempPath(), $"iteration_%d{tmpFileCounter.Count ()}.tmp")
    let tmpFileName =
        match outputPath with
        | Some outputDirectory when Path.EndsInDirectorySeparator(outputDirectory) ->
            fun () -> Path.Combine(outputDirectory, Path.GetFileName(tmpFileName ()))
        | Some path -> fun () -> path
        | None -> tmpFileName
        >> fun dstPath -> Path.ChangeExtension(dstPath, solver.FileExtension)
    let performTransformation performer commands =
        let dstPath = tmpFileName ()
        let srcPath = Path.ChangeExtension(dstPath, $".input%s{solver.FileExtension}")
        let lines = List.map toString commands
        Program.SaveFile srcPath lines
        performer commands srcPath dstPath
    let runTransformation =
        let performer commands srcPath dstPath =
            match transformer with
            | Some transformer -> if transformer.PerformTransform InteractiveRun commands dstPath then Some dstPath else None
            | None -> Some srcPath
        performTransformation performer
    let runOn commands =
        opt {
            let! transformedPath = runTransformation commands
            let! path'' = solver.Run transformedPath outputPath
            print_verbose $"%s{solver.Name} run on %s{transformedPath} and the result is saved at %s{path''}"
            return ()
        } |> Option.defaultWith (fun () -> print_verbose "unknown")

    let parser = SMTExpr.Parser()
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

let private solve_from_path (solver : SolverProgramRunner) (transformer : TransformerProgram option) outputPath (options : ParseResults<SolveArguments>) path =
    let path' =
        match transformer with
        | Some transformer -> transformer.Run path outputPath
        | None -> Some path
    match path' with
    | None -> printfn "unknown" // no transformation, no solving
    | Some path' ->
    match solver.Run path' outputPath with
    | None -> printfn "unknown"
    | Some path'' ->
    print_verbose $"%s{solver.Name} run on %s{path'} and the result is saved at %s{path''}"
    if not <| options.Contains(Table) then () else
    let table_path = solver.AddResultsToTable path path' path''
    print_verbose $"Saved run result at %s{table_path}"

let private solve outputPath runSame (options : ParseResults<SolveArguments>) =
    let solver_name = options.GetResult(Solver)
    let solver = solverByName solver_name
    let transformer =
        match options.TryGetResult(Transform) with
        | Some _ as transformOptions ->
            let mode = solverNameToTransformMode solver_name
            modeToTransformerProgram mode transformOptions runSame |> fst |> Some
        | None -> None
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
    let transArgs = No_Isolation :: transArgs
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

    override x.TargetPath path = path

[<EntryPoint>]
let main args =
    let parser = ArgumentParser.Create<CLIArguments>(programName = "ringen")
    let parseResults = parser.ParseCommandLine(inputs = args).GetAllResults()
    if List.contains Quiet parseResults then VERBOSITY_MODE <- QUIET_MODE
    SECONDS_TIMEOUT <- List.tryPick (function Timelimit tl -> Some tl | _ -> None) parseResults |> Option.defaultValue 300
    let outputPath = List.tryPick (function Output_path dir -> Some dir | _ -> None) parseResults
    let runSame transArgs mode = SelfProgramRunner(parser, parseResults, transArgs, mode) :> ProgramRunner
    match List.find (function Transform _ | Solve _ -> true | _ -> false) parseResults with
    | Transform args -> transform outputPath runSame args
    | Solve args -> solve outputPath runSame args
    | _ -> __unreachable__()
    0
