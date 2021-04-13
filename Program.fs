module RInGen.Program

open System
open RInGen.Solvers
open CommandLine

[<Verb("solve", HelpText = "Transform and run solver")>]
type solveOptions = {
    [<Option("no-transform", HelpText = "Just run a solver with no transformation")>] notransform : bool
    [<Option("tipToHorn", HelpText = "Convert TIP-like systems to Horn clauses")>] tipToHorn : bool
    [<Option('t', "timelimit", HelpText = "Time limit, in seconds (default 300)")>] timelimit : int option
    [<Option('q', "quiet", HelpText = "Quiet mode")>] quiet : bool
    [<Option('o', "output-directory", HelpText = "Output directory where to put a transformed file (default: same as input PATH)")>] output : string option
    [<Value(0, MetaValue = "SOLVER_NAME", Required = true, HelpText = "Run a specific solver (one of: z3 | eldarica | cvc4f | cvc4ind | verimap | all) after processing")>] solver : string
    [<Value(1, MetaValue = "PATH", Required = true, HelpText = "Full path to file or directory")>] path : string
}

[<Verb("transform", HelpText = "Generate CHCs based on the benchmark")>]
type transformOptions = {
    [<Option("sorts", HelpText = "Convert ADTs to sorts")>] tosorts : bool
    [<Option("tipToHorn", HelpText = "Convert TIP-like systems to Horn clauses")>] tipToHorn : bool
    [<Option('q', "quiet", HelpText = "Quiet mode")>] quiet : bool
    [<Option('o', "output-directory", HelpText = "Output directory where to put a transformed file (default: same as input PATH)")>] output : string option
    [<Value(0, MetaValue = "PATH", Required = true, HelpText = "Full path to file or directory")>] path : string
}

let solverByName (solverName : string) =
    let solverName = solverName.ToLower().Trim()
    match () with
    | _ when solverName = "z3" -> Z3Solver() :> ISolver
    | _ when solverName = "eldarica" -> EldaricaSolver() :> ISolver
    | _ when solverName = "cvc4ind" -> CVC4IndSolver() :> ISolver
    | _ when solverName = "verimap" -> VeriMAPiddtSolver() :> ISolver
    | _ when solverName = "cvc4f" -> CVC4FiniteSolver() :> ISolver
    | _ when solverName = "all" -> AllSolver() :> ISolver
    | _ -> failwithf $"Unknown solver: %s{solverName}. Specify one of: z3, eldarica, cvc4f, cvc4ind, verimap, all."

let solve (solveOptions : solveOptions) =
    match solveOptions.timelimit with
    | Some timelimit -> SolverResult.SECONDS_TIMEOUT <- timelimit
    | None -> ()
    let solver = solverByName solveOptions.solver
    let force = true
    solver.TransformAndRunOnBenchmark (not solveOptions.notransform) solveOptions.tipToHorn solveOptions.quiet force solveOptions.path solveOptions.output

let transform (transformOptions : transformOptions) =
    let solver = if transformOptions.tosorts then SortHornTransformer() :> ITransformer else ADTHornTransformer() :> ITransformer
    solver.TransformBenchmark true transformOptions.tipToHorn transformOptions.quiet false transformOptions.path transformOptions.output

[<EntryPoint>]
let main args =
    Parser.Default.ParseArguments<solveOptions,transformOptions>(args)
        .WithParsed<solveOptions>(Action<_> solve)
        .WithParsed<transformOptions>(Action<_> transform)
    |> ignore
    0
