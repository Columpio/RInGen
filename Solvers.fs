module FLispy.Solvers
open System.IO
open System.Collections
open System.Diagnostics

let SECONDS_TIMEOUT = 30

type SolverResult = SAT | UNSAT | ERROR of string | UNKNOWN | TIMELIMIT

[<AbstractClass>]
type ISolver() =
    abstract member SetupProcess : ProcessStartInfo -> string -> unit
    abstract member InterpretResult : string list -> SolverResult

    member x.Solve filename =
        use p = new Process()
//        p.StartInfo.WorkingDirectory <- Path.Combine(__SOURCE_DIRECTORY__, "foreign_solvers")
        p.StartInfo.RedirectStandardOutput <- true
        p.StartInfo.RedirectStandardError <- true
        p.StartInfo.UseShellExecute <- false
        x.SetupProcess p.StartInfo filename
        p.Start() |> ignore
        let output = Generic.List<string>()
        let error = Generic.List<string>()
        let addToList (l : Generic.List<_>) x = if x <> null then l.Add x
        p.OutputDataReceived.Add(fun args -> addToList output args.Data)
        p.ErrorDataReceived.Add(fun args -> addToList error args.Data)
        p.BeginErrorReadLine()
        p.BeginOutputReadLine()
        let exited = p.WaitForExit(SECONDS_TIMEOUT * 1000)
        if not exited then
            p.Kill()
            TIMELIMIT
        elif error.Count > 0 then
            ERROR(join "\n" error)
        else x.InterpretResult (List.ofSeq output)
    
    member x.SolveWithTime filename =
        let timer = Stopwatch()
        timer.Start()
        let result = x.Solve filename
        result, timer.ElapsedMilliseconds

type CVC4FiniteSolver () =
    inherit ISolver()

    override x.SetupProcess pi filename =
        pi.FileName <- "cvc4"
        pi.Arguments <- sprintf "--finite-model-find %s" filename

    override x.InterpretResult output =
        SAT