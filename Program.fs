module RInGen.Program

open System
open RInGen.Solvers
open CommandLine

[<Verb("solve", HelpText = "Transform and run solver")>]
type solveOptions = {
    [<Option("no-transform", HelpText = "Just run a solver with no transformation")>] notransform : bool
    [<Option("tip", HelpText = "Convert TIP-like systems to Horn clauses")>] tip : bool
    [<Option('s', "sync-terms", HelpText = "Synchronize terms of a CHC system")>] sync_terms : bool
    [<Option('e', "keep-exist-quantifiers", HelpText = "Handle existential quantifiers (instead of sound halting with `unknown`)")>] keep_exists : bool
    [<Option('t', "timelimit", HelpText = "Time limit, in seconds (default 300)")>] timelimit : int option
    [<Option('q', "quiet", HelpText = "Quiet mode")>] quiet : bool
    [<Option('f', "force", HelpText = "Force benchmark generation")>] force : bool
    [<Option('r', "rerun", HelpText = "Rerun if answer was SAT")>] rerun : bool
    [<Option("table", HelpText = "Generate .csv statistics table after solving")>] table : bool
    [<Option('o', "output-directory", HelpText = "Output directory where to put a transformed file (default: same as input PATH)")>] output : string option
    [<Value(0, MetaValue = "SOLVER_NAME", Required = true, HelpText = "Run a specific solver (one of: myz3 | z3 | eldarica | cvc4f | cvc4ind | verimap | vampire | all) after processing")>] solver : string
    [<Value(1, MetaValue = "PATH", Required = true, HelpText = "Full path to file or directory")>] path : string
}

[<Verb("transform", HelpText = "Generate CHCs based on the benchmark")>]
type transformOptions = {
    [<Option("sorts", HelpText = "Convert ADTs to sorts")>] tosorts : bool
    [<Option("tip", HelpText = "Convert TIP-like systems to Horn clauses")>] tip : bool
    [<Option('s', "sync-terms", HelpText = "Synchronize terms of a CHC system")>] sync_terms : bool
    [<Option('q', "quiet", HelpText = "Quiet mode")>] quiet : bool
    [<Option('o', "output-directory", HelpText = "Output directory where to put a transformed file (default: same as input PATH)")>] output : string option
    [<Value(0, MetaValue = "PATH", Required = true, HelpText = "Full path to file or directory")>] path : string
}

let solverByName (solverName : string) =
    let solverName = solverName.ToLower().Trim()
    match () with
    | _ when solverName = "myz3" -> MyZ3Solver() :> ISolver
    | _ when solverName = "z3" -> Z3Solver() :> ISolver
    | _ when solverName = "eldarica" -> EldaricaSolver() :> ISolver
    | _ when solverName = "cvc4ind" -> CVC4IndSolver() :> ISolver
    | _ when solverName = "verimap" -> VeriMAPiddtSolver() :> ISolver
    | _ when solverName = "vampire" -> VampireSolver() :> ISolver
    | _ when solverName = "cvc4f" -> CVC4FiniteSolver() :> ISolver
    | _ when solverName = "all" -> AllSolver() :> ISolver
    | _ -> failwithf $"Unknown solver: %s{solverName}. Specify one of: myz3, z3, eldarica, cvc4f, cvc4ind, verimap, vampire, all."

let solve (solveOptions : solveOptions) =
    match solveOptions.timelimit with
    | Some timelimit -> SECONDS_TIMEOUT <- timelimit
    | None -> ()
    if solveOptions.quiet then VERBOSITY_MODE <- QUIET_MODE
    let solver = solverByName solveOptions.solver
    let options = {
        transform=not solveOptions.notransform
        table=solveOptions.table
        tip=solveOptions.tip
        sync_terms=solveOptions.sync_terms
        keep_exists=solveOptions.keep_exists
        force=solveOptions.force
        path=solveOptions.path
        output=solveOptions.output
        rerun=solveOptions.rerun
    }
    solver.TransformAndRunOnBenchmark options

let transform (transformOptions : transformOptions) =
    if transformOptions.quiet then VERBOSITY_MODE <- QUIET_MODE
    let solver = if transformOptions.tosorts then SortHornTransformer() :> ITransformer else ADTHornTransformer() :> ITransformer
    let options = {
        transform=true
        table=false
        tip=transformOptions.tip
        sync_terms=transformOptions.sync_terms
        keep_exists=true
        force=false
        path=transformOptions.path
        output=transformOptions.output
        rerun=false
    }
    solver.TransformBenchmark options

[<EntryPoint>]
let main args =
    Parser.Default.ParseArguments<solveOptions,transformOptions>(args)
        .WithParsed<solveOptions>(Action<_> solve)
        .WithParsed<transformOptions>(Action<_> transform)
    |> ignore
    0
