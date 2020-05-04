module FLispy.Solvers
open System.IO
open System.Collections
open System.Diagnostics
open System

let SECONDS_TIMEOUT = 3
let MSECONDS_TIMEOUT = SECONDS_TIMEOUT * 1000

type SolverResult = SAT | UNSAT | ERROR of string | UNKNOWN of string | TIMELIMIT

[<AbstractClass>]
type ISolver() =
    abstract member SetupProcess : ProcessStartInfo -> string -> unit
    abstract member InterpretResult : string -> SolverResult

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
        elif error <> "" then
            ERROR(error)
        else x.InterpretResult output

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

    override x.SetupProcess pi filename =
        pi.FileName <- "cvc4"
        pi.Arguments <- sprintf "--finite-model-find --tlimit=%d %s" MSECONDS_TIMEOUT filename

    override x.InterpretResult raw_output =
        let output = split raw_output
        match output with
        | line::_ when line.StartsWith("(error ") -> ERROR(raw_output)
        | line::_ when line = "sat" -> SAT
        | line::_ when line = "unsat" -> UNSAT
        | line::reason::_ when line = "unknown" -> UNKNOWN reason
        | _ -> UNKNOWN raw_output

type EldaricaSolver () =
    inherit ISolver()
    override x.SetupProcess pi filename =
        pi.FileName <- "eld"
        pi.Arguments <- sprintf "-horn -hsmt -t:%d %s" SECONDS_TIMEOUT filename

    override x.InterpretResult raw_output =
        let output = split raw_output
        match output with
        | _ -> UNKNOWN raw_output
