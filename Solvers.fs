module FLispy.Solvers
open System.IO
open System.Diagnostics
open System
open Lexer

let SECONDS_TIMEOUT = 3 // 5 * 60
let MSECONDS_TIMEOUT = SECONDS_TIMEOUT * 1000

type SolverResult = SAT | UNSAT | ERROR of string | UNKNOWN of string | TIMELIMIT

let rec private hasInt = function
    | PList es -> List.exists hasInt es
    | PNumber _ -> true
    | PComment -> false
    | PMatch(t, ts) -> hasInt t || List.exists (fun (a, b) -> hasInt a || hasInt b) ts
    | PSymbol "Int" -> true
    | PSymbol _ -> false

let parse_file filename =
    let text = sprintf "(%s)" <| System.IO.File.ReadAllText(filename)
    try
        let (PList exprs) = parse_string text
        exprs |> List.filter ((<>) PComment)
    with _ -> printfn "%s" filename; reraise ()

[<AbstractClass>]
type ISolver() =
    abstract member SetupProcess : ProcessStartInfo -> string -> unit
    abstract member InterpretResult : string -> string -> SolverResult
    abstract member Name : string
    abstract member CodeTransformation : int -> ParseExpression list -> command list list

    member x.GenerateClauses directory to_clauses =
        let mutable files = 0
        let mutable successful = 0
        let mutable total_generated = 0
        let mapFile (src : string) dst =
            if src.EndsWith(".smt2") then
    //            printfn "Transforming: %s" src
                files <- files + 1
                let exprs = parse_file src
                try
                    if not <| List.exists hasInt exprs then
                        let newTests = x.CodeTransformation to_clauses exprs
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

    member x.RunOnBenchmarkSet dir =
        let run_file src dst =
            try
                printfn "Running %s on %s" x.Name src
                let answer, time = x.SolveWithTime(src)
                File.WriteAllText(dst, sprintf "%d,%O" time answer)
            with e -> printfn "Exception in %s: %s" src dst
        walk_through dir (sprintf ".%sAnswers" x.Name) run_file

    member x.Solve (filename : string) =
        use p = new Process()
        p.StartInfo.WorkingDirectory <- Path.GetDirectoryName(filename)
        p.StartInfo.RedirectStandardOutput <- true
        p.StartInfo.RedirectStandardError <- true
        p.StartInfo.UseShellExecute <- false
        x.SetupProcess p.StartInfo filename
        p.Start() |> ignore
//        let output = Generic.List<string>()
//        let error = Generic.List<string>()
//        let addToList (l : Generic.List<_>) x = if x <> null then l.Add x
//        p.OutputDataReceived.Add(fun args -> addToList output args.Data)
//        p.ErrorDataReceived.Add(fun args -> addToList error args.Data)
//        p.BeginErrorReadLine()
//        p.BeginOutputReadLine()
        let output = p.StandardOutput.ReadToEnd()
        let error = p.StandardError.ReadToEnd()
        let exited = p.WaitForExit(MSECONDS_TIMEOUT)
        if not exited then
            p.Kill()
            TIMELIMIT
        else x.InterpretResult error output

    member x.SolveWithTime filename =
        let timer = Stopwatch()
        timer.Start()
        let result = x.Solve filename
        let time = int timer.ElapsedMilliseconds
        let time = min time MSECONDS_TIMEOUT
        match result with
        | UNKNOWN _ when time = MSECONDS_TIMEOUT -> TIMELIMIT, time
        | _ -> result, time

let private split (s : string) = s.Split(Environment.NewLine.ToCharArray()) |> List.ofArray

type CVC4FiniteSolver () =
    inherit ISolver()

    override x.Name = "CVC4Finite"

    override x.CodeTransformation to_clauses exprs =
        let setOfCHCSystems = ParseExtension.functionsToClauses id exprs // (fun t -> Hence(t, falsee)) exprs
        let set_logic_all = SetLogic "ALL"
        setOfCHCSystems
        |> List.map (fun chcSystem -> List.collect ParseExtension.to_sorts chcSystem)
        |> List.map (fun chcSystem -> chcSystem |> List.filter (function SetLogic _ -> false | _ -> true))
        |> List.map (fun chcSystem -> set_logic_all :: chcSystem)

    override x.SetupProcess pi filename =
        pi.FileName <- "cvc4"
        pi.Arguments <- sprintf "--finite-model-find --tlimit=%d %s" MSECONDS_TIMEOUT filename

    override x.InterpretResult error raw_output =
        if error <> "" then ERROR(error) else
        let output = split raw_output
        match output with
        | line::_ when line.StartsWith("(error ") -> ERROR(raw_output)
        | line::_ when line = "sat" -> SAT
        | line::_ when line = "unsat" -> UNSAT
        | line::reason::_ when line = "unknown" -> UNKNOWN reason
        | _ -> UNKNOWN raw_output


type EldaricaSolver () =
    inherit ISolver()

    override x.Name = "Eldarica"

    override x.CodeTransformation to_clauses exprs = ParseExtension.functionsToClauses id exprs // (fun t -> Hence(t, falsee)) exprs

    override x.SetupProcess pi filename =
        pi.FileName <- "/home/columpio/Documents/eldarica/eld"
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
    inherit ISolver()

    override x.Name = "Z3"

    override x.CodeTransformation to_clauses exprs = ParseExtension.functionsToClauses id exprs

    override x.SetupProcess pi filename =
        pi.FileName <- "/usr/bin/z3"
        pi.Arguments <- sprintf "-smt2 -nw -T:%d %s" SECONDS_TIMEOUT filename

    override x.InterpretResult error raw_output =
        let output = split raw_output
        match output with
        | line::_ when line = "timeout" -> TIMELIMIT
        | _ -> UNKNOWN (error + " &&& " + raw_output)
