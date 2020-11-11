module FLispy.Solvers
open System.IO
open System.Diagnostics
open System
open Lexer
open SolverResult

let rec private isBadBenchmark = function
    | PList [PSymbol "declare-sort"; _; _] -> false
    | PList [PSymbol "declare-fun"; _; _; _] -> true
    | PList es -> List.exists isBadBenchmark es
    | PNumber _ -> true
    | PComment -> false
    | PMatch(t, ts) -> isBadBenchmark t || List.exists (fun (a, b) -> isBadBenchmark a || isBadBenchmark b) ts
    | PSymbol "Int" -> true
    | PSymbol _ -> false

let parse_file filename =
    let rec filterComments = function
        | PList es -> es |> List.filter ((<>) PComment) |> List.map filterComments |> PList
        | PMatch(t, ts) -> PMatch(filterComments t, ts |> List.map (fun (p, e) -> filterComments p, filterComments e))
        | PNumber _
        | PSymbol _ as e -> e
        | PComment -> __unreachable__()
    let text = sprintf "(%s)" <| File.ReadAllText(filename)
    try
        let (PList exprs) = filterComments <| parse_string text
        exprs
    with _ -> printfn "%s" filename; reraise ()

[<AbstractClass>]
type ISolver() =
    abstract member SetupProcess : ProcessStartInfo -> string -> unit
    abstract member InterpretResult : string -> string -> SolverResult
    abstract member Name : string
    abstract member CodeTransformation : bool -> ParseExpression list -> command list list

    member x.GenerateClausesSingle tipToHorn filename =
        let exprs = parse_file filename
        if List.exists isBadBenchmark exprs then
            failwithf "Syntax error in %s" filename
        else
        let transformed = x.CodeTransformation tipToHorn exprs
        let paths =
            seq {
                for testIndex, newTest in List.indexed transformed do
                    let lines = List.map toString newTest
                    let path = Path.ChangeExtension(filename, sprintf ".%s.%d.smt2" x.Name testIndex)
                    File.WriteAllLines(path, lines)
                    yield path
            } |> List.ofSeq
        paths

    abstract GenerateClauses : bool -> bool -> string -> string
    default x.GenerateClauses tipToHorn force directory =
        let mutable files = 0
        let mutable successful = 0
        let mutable total_generated = 0
        let mapFile (src : string) dst =
            if src.EndsWith(".smt2") then
    //            printfn "Transforming: %s" src
                files <- files + 1
                let exprs = parse_file src
                try
                    if force || not <| List.exists isBadBenchmark exprs then
                        let newTests = x.CodeTransformation tipToHorn exprs
                        for testIndex, newTest in List.indexed newTests do
                            let lines = List.map toString newTest
                            let path = Path.ChangeExtension(dst, sprintf ".%d.smt2" testIndex)
                            File.WriteAllLines(path, lines)
                            total_generated <- total_generated + 1
                    successful <- successful + 1
                with e -> printfn "Exception in %s: %O" src e.Message
        let output_directory = walk_through directory ("." + x.Name) mapFile
        printfn "All files:       %d" files
        printfn "Successful:      %d" successful
        printfn "Total generated: %d" total_generated
        output_directory

    abstract member RunOnBenchmarkSet : bool -> string -> string
    default x.RunOnBenchmarkSet overwrite dir =
        let run_file src dst =
            if overwrite || not <| File.Exists(dst) then
                try
                    printfn "Running %s on %s" x.Name src
                    let answer, time = x.SolveWithTime(src)
                    File.WriteAllText(dst, sprintf "%d,%O" time answer)
                with e -> printfn "Exception in %s: %s" src dst
            else printfn "%s skipping %s (answer exists)" x.Name src
        walk_through dir (sprintf ".%sAnswers" x.Name) run_file

    abstract member Solve : string -> SolverResult
    default x.Solve (filename : string) =
        use p = new Process()
        p.StartInfo.WorkingDirectory <- Path.GetDirectoryName(filename)
        p.StartInfo.RedirectStandardOutput <- true
        p.StartInfo.RedirectStandardError <- true
        p.StartInfo.UseShellExecute <- false
        x.SetupProcess p.StartInfo filename
        p.Start() |> ignore
        let output = p.StandardOutput.ReadToEnd()
        let error = p.StandardError.ReadToEnd()
        let exited = p.WaitForExit(MSECONDS_TIMEOUT ())
        if not exited then
            p.Kill()
            TIMELIMIT
        else x.InterpretResult error output

    member x.SolveWithTime filename =
        printfn "Solving %s with timelimit %d seconds" filename SECONDS_TIMEOUT
        let timer = Stopwatch()
        timer.Start()
        let result = x.Solve filename
        let time = int timer.ElapsedMilliseconds
        let time = min time (MSECONDS_TIMEOUT ())
        match result with
        | UNKNOWN _ when time = MSECONDS_TIMEOUT () -> TIMELIMIT, time
        | _ -> result, time

    member x.EncodeSingleFile tipToHorn filename = filename |> parse_file |> x.CodeTransformation tipToHorn |> List.head

let private split (s : string) = s.Split(Environment.NewLine.ToCharArray()) |> List.ofArray

type CVC4FiniteSolver () =
    inherit ISolver()

    override x.Name = "CVC4Finite"

    override x.CodeTransformation tipToHorn exprs =
        let setOfCHCSystems = ParseExtension.functionsToClauses tipToHorn exprs
        let set_logic_all = SetLogic "ALL"
        setOfCHCSystems
        |> List.map (fun chcSystem -> List.collect ParseExtension.to_sorts chcSystem)
        |> List.map (fun chcSystem -> chcSystem |> List.filter (function SetLogic _ -> false | _ -> true))
        |> List.map (fun chcSystem -> set_logic_all :: chcSystem)

    override x.SetupProcess pi filename =
        pi.FileName <- "cvc4"
        pi.Arguments <- sprintf "--finite-model-find --tlimit=%d %s" (MSECONDS_TIMEOUT ()) filename

    override x.InterpretResult error raw_output =
        if error <> "" then ERROR(error) else
        let output = split raw_output
        match output with
        | line::_ when line.StartsWith("(error ") -> ERROR(raw_output)
        | line::_ when line = "sat" -> SAT
        | line::_ when line = "unsat" -> UNSAT
        | line::reason::_ when line = "unknown" && reason = "(:reason-unknown timeout)" -> TIMELIMIT
        | line::reason::_ when line = "unknown" -> UNKNOWN reason
        | _ -> UNKNOWN raw_output


[<AbstractClass>]
type IADTSolver () =
    inherit ISolver()

    override x.CodeTransformation tipToHorn exprs =
        let setOfCHCSystems = ParseExtension.functionsToClauses tipToHorn exprs
        let set_logic = SetLogic "HORN"
        setOfCHCSystems
        |> List.map (fun chcSystem -> chcSystem |> List.filter (function SetLogic _ -> false | _ -> true))
        |> List.map (fun chcSystem -> set_logic :: chcSystem)


type EldaricaSolver () =
    inherit IADTSolver()

    override x.Name = "Eldarica"

    override x.SetupProcess pi filename =
        pi.FileName <- "eld"
        pi.Arguments <- sprintf "-horn -hsmt -t:%d %s" SECONDS_TIMEOUT filename

    override x.InterpretResult error raw_output =
        let output = split raw_output
        match output with
        | line::_ when line.StartsWith("(error") -> ERROR raw_output
        | line::_ when line = "unknown" -> UNKNOWN raw_output
        | line::_ when line = "sat" -> SAT
        | line::_ when line = "unsat" -> UNSAT
        | _ -> UNKNOWN (error + " &&& " + raw_output)


type Z3Solver () =
    inherit IADTSolver()

    override x.Name = "Z3"

    override x.SetupProcess pi filename =
        pi.FileName <- "z3"
        pi.Arguments <- sprintf "-smt2 -nw -memory:%d -T:%d %s" MEMORY_LIMIT_MB SECONDS_TIMEOUT filename

    override x.InterpretResult error raw_output =
        let output = split raw_output
        match output with
        | line::_ when line = "timeout" -> TIMELIMIT
        | line::_ when line = "unsat" -> UNSAT
        | _ when error = "" && raw_output = "" -> OUTOFMEMORY
        | _ -> UNKNOWN (error + " &&& " + raw_output)

type CVC4IndSolver () =
    inherit IADTSolver()

    override x.Name = "CVC4Ind"

    override x.SetupProcess pi filename =
        pi.FileName <- "cvc4"
        pi.Arguments <- sprintf "--quant-ind --quant-cf --conjecture-gen --conjecture-gen-per-round=3 --full-saturate-quant --tlimit=%d %s" (MSECONDS_TIMEOUT ()) filename

    override x.InterpretResult error raw_output =
        if error <> "" then ERROR(error) else
        let output = split raw_output
        match output with
        | line::_ when line.StartsWith("(error ") -> ERROR(raw_output)
        | line::_ when line = "sat" -> SAT
        | line::_ when line = "unsat" -> UNSAT
        | line::reason::_ when line = "unknown" && reason = "(:reason-unknown timeout)" -> TIMELIMIT
        | line::reason::_ when line = "unknown" -> UNKNOWN reason
        | _ -> UNKNOWN raw_output

type AllSolver () =
    inherit ISolver()
    let solvers : ISolver list = [Z3Solver(); EldaricaSolver(); CVC4IndSolver(); CVC4FiniteSolver()]

    override x.Name = "AllSolvers"
    override x.SetupProcess _ _ = __unreachable__()
    override x.InterpretResult _ _ = __unreachable__()
    override x.CodeTransformation _ _ = __unreachable__()

    override x.Solve filename =
        for solver in solvers do solver.Solve(filename) |> ignore
        UNKNOWN "All solvers"

    override x.GenerateClauses tipToHorn force directory =
        let paths = solvers |> List.map (fun solver -> printfn "Generating clauses for %s" solver.Name; solver.GenerateClauses tipToHorn force directory)
        join ";;;" paths

    override x.RunOnBenchmarkSet overwrite directory =
        let runs = directory.Split(";;;") |> List.ofArray |> List.zip solvers
        let results = runs |> List.map (fun (solver, path) -> solver.RunOnBenchmarkSet overwrite path)
        let names = solvers |> List.map (fun solver -> solver.Name)
        ResultTable.PrintReadableResultTable names results
        directory