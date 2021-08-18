module RInGen.Main

open RInGen.Transformers
open RInGen.Solvers
open Argu

type private TransformMode =
    | Original
    | FreeSorts
    | Prolog

type private LocalTransformArguments =
    | [<Unique>] Tip
    | [<Unique; AltCommandLine("-s")>] Sync_terms

    interface IArgParserTemplate with
        member x.Usage =
            match x with
            | Tip -> "Negates the query (for TIP benchmarks)"
            | Sync_terms -> "Synchronize terms of a CHC system"

let private getLocalTransformOptions = function
    | Some (options : ParseResults<_>) -> {tip=options.Contains(Tip); sync_terms=options.Contains(Sync_terms)}
    | None -> {tip=false; sync_terms=false}

type private TransformArguments =
    | [<Unique; AltCommandLine("-m")>] Mode of TransformMode
    | [<Unique; Last; AltCommandLine("-t"); SubCommand>] Transform_options of ParseResults<LocalTransformArguments>
    | [<MainCommand; ExactlyOnce>] Path of PATH:path

    interface IArgParserTemplate with
        member x.Usage =
            match x with
            | Mode _ -> "Transformation mode: keep `original` smt2 declarations; transform ADTs to `free sorts` in smt2; transform to `Prolog` clauses (default: original)"
            | Transform_options _ -> "Apply additional transformations to the problem"
            | Path _ -> "Full path to file or directory"

let private print_transformation_success path = function
    | Some path' -> print_verbose $"Transformation run on %s{path} and the result is saved at %s{path'}"
    | None -> () // if the run was not successful, we have already printed the reason

let private transform outputDirectory (options : ParseResults<TransformArguments>) =
    let transformOptions = options.TryGetResult(Transform_options) |> getLocalTransformOptions
    let path = options.GetResult(Path)
    let program =
        match options.GetResult(Mode, defaultValue = Original) with
        | Original -> OriginalTransformerProgram(transformOptions) :> TransformerProgram
        | FreeSorts -> FreeSortsTransformerProgram(transformOptions) :> TransformerProgram
        | Prolog -> PrologTransformerProgram(transformOptions) :> TransformerProgram
    let path' = program.Run path outputDirectory
    if IN_VERBOSE_MODE () then print_transformation_success path path'
    elif IN_QUIET_MODE () then printfn $"""%s{Option.defaultValue "" path'}"""

type private SolverName =
    | Z3
    | Eldarica
    | CVC_FMF
    | CVC_Ind
    | VeriMAP
    | Vampire
    | MyZ3
//    | All

type private SolveArguments =
    | [<Unique; Last; AltCommandLine("-t"); SubCommand>] Transform of ParseResults<LocalTransformArguments>
//    | [<Unique; AltCommandLine("-e")>] Keep_exist_quantifiers
    | [<Unique>] Timelimit of int
    | [<Unique>] Table
    | [<MainCommand; ExactlyOnce>] Required of SOLVER_NAME:SolverName * PATH:path

    interface IArgParserTemplate with
        member x.Usage =
            match x with
//            | Keep_exist_quantifiers -> "Handle existential quantifiers (instead of sound halting with `unknown`)"
            | Timelimit _ -> "Time limit, in seconds (default: 300)"
            | Required _ -> "Run a specific solver `SOLVER NAME` on file(s) from `PATH`"
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
//    | All -> AllSolver() :> SolverProgramRunner

let private transformerForSolver transformOptions = function
    | MyZ3
    | Z3
    | Eldarica
    | CVC_Ind -> OriginalTransformerProgram(transformOptions) :> TransformerProgram
    | VeriMAP -> PrologTransformerProgram(transformOptions) :> TransformerProgram
    | Vampire
    | CVC_FMF -> FreeSortsTransformerProgram(transformOptions) :> TransformerProgram

let private solve outputDirectory (options : ParseResults<SolveArguments>) =
    SECONDS_TIMEOUT <- options.GetResult(Timelimit, defaultValue = 300)
    let solver_name, path = options.GetResult(Required)
    let solver = solverByName solver_name
    let path' =
        match options.TryGetResult(Transform) with
        | Some _ as transformOptions -> // need transformation
            let transformOptions = getLocalTransformOptions transformOptions
            let transformer = transformerForSolver transformOptions solver_name
            let path' = transformer.Run path outputDirectory
            print_transformation_success path path'
            path'
        | None -> Some path // only run
    match path' with
    | None -> () // no transformation, no solving
    | Some path' ->
    match solver.Run path' outputDirectory with
    | None -> ()
    | Some path'' ->
    print_verbose $"%s{solver.Name} run on %s{path'} and the result is saved at %s{path''}"
    if not <| options.Contains(Table) then () else
    let table_path = solver.AddResultsToTable path path' path''
    print_verbose $"Saved run result at %s{table_path}"

type private CLIArguments =
    | [<Unique; AltCommandLine("-q")>] Quiet
    | [<Unique; AltCommandLine("-o")>] Output_directory of PATH:path
    | [<CliPrefix(CliPrefix.None); SubCommand>] Transform of ParseResults<TransformArguments>
    | [<CliPrefix(CliPrefix.None); SubCommand>] Solve of ParseResults<SolveArguments>

    interface IArgParserTemplate with
        member this.Usage =
            match this with
            | Transform _ -> "Transform SMTLIB2 file(s) into constrained Horn clauses"
            | Solve _ -> "Transform SMTLIB2 file(s) and run solver"
            | Quiet -> "Quiet mode"
            | Output_directory _ -> "Output directory where to put new files (default: same as input PATH)"

[<EntryPoint>]
let main args =
    let parseResults = ArgumentParser.Create<CLIArguments>().ParseCommandLine(inputs = args)
    if parseResults.Contains(Quiet) then VERBOSITY_MODE <- QUIET_MODE
    let outputDirectory = parseResults.TryGetResult(Output_directory)
    match parseResults.GetSubCommand() with
    | Transform args -> transform outputDirectory args
    | Solve args -> solve outputDirectory args
    | _ -> __unreachable__()
    0
