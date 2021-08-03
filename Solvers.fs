module RInGen.Solvers
open System
open System.IO
open System.Diagnostics
open System.Text
open System.Text.RegularExpressions
open SolverResult

type solvingOptions =
    {
        transform : bool
        tip : bool
        sync_terms : bool
        keep_exists : bool
        rerun : bool
        force : bool
        path : string
        output : string option
    }

let private isBadBenchmark cmnds =
    let hasDefines = List.exists (function Definition _ -> true | _ -> false) cmnds
    let hasDeclareFuns = List.exists (function Command (DeclareFun _) -> true | _ -> false) cmnds
    hasDefines && hasDeclareFuns

let private containsExistentialClauses =
    let rec containsExistentialClauses = function
        | BaseRule _ -> false
        | ExistsRule _ -> true
        | ForallRule(_, r) -> containsExistentialClauses r
    let containsExistentialClauses = function
        | TransformedCommand r -> containsExistentialClauses r
        | _ -> false
    List.exists containsExistentialClauses

let private isNonLinearCHCSystem =
    let rec isNonLinearClause = function
        | BaseRule(atoms, _) ->
            atoms |> Seq.filter (function AApply _ -> true | _ -> false) |> Seq.length |> (<) 1
        | ExistsRule(_, r)
        | ForallRule(_, r) -> isNonLinearClause r
    let isNonLinearCommand = function
        | TransformedCommand r -> isNonLinearClause r
        | _ -> false
    List.exists isNonLinearCommand

let private cleanCommands keepExists set_logic chcSystem =
    let filt = function
        | OriginalCommand(SetLogic _)
        | OriginalCommand(GetInfo _)
        | OriginalCommand GetModel
        | OriginalCommand CheckSat
        | OriginalCommand Exit -> false
        | _ -> true
    let chcSystem = chcSystem |> List.filter filt
    let commands = OriginalCommand set_logic :: chcSystem @ [OriginalCommand CheckSat]
    if not keepExists && containsExistentialClauses commands then [] else [commands]

type ITransformer =
    abstract member TransformBenchmark : solvingOptions -> unit
    abstract member TransformClauses : bool -> transformedCommand list -> transformedCommand list list

[<AbstractClass>]
type IDirectoryTransformer<'directory> () =
    abstract member GenerateClauses : solvingOptions -> 'directory
    abstract member TransformClauses : bool -> transformedCommand list -> transformedCommand list list

    member x.TransformBenchmarkAndReturn (opts : solvingOptions) =
        let outputDirectory = x.GenerateClauses opts
        if IN_VERBOSE_MODE () then printfn $"CHC systems of directory %s{opts.path} are preprocessed and saved in {outputDirectory}"
        outputDirectory

    interface ITransformer with
        member x.TransformBenchmark opts =
            match () with
            | _ when File.Exists(opts.path) ->
                let outputFiles = x.GenerateClausesSingle opts
                match outputFiles with
                | [] -> printfn "unknown"
                | [outputFile] ->
                    if IN_VERBOSE_MODE () then printfn $"CHC system in %s{opts.path} is preprocessed and saved in %s{outputFile}"
                    else printfn $"%s{outputFile}"
                | _ ->
                    if IN_VERBOSE_MODE () then printfn $"Preprocessing of %s{opts.path} produced %d{List.length outputFiles} files:"
                    if IN_VERBOSE_MODE () then List.iter (printfn "%s") outputFiles
            | _ when Directory.Exists(opts.path) -> x.TransformBenchmarkAndReturn opts |> ignore
            | _ -> failwithf $"There is no such file or directory: %s{opts.path}"
        member x.TransformClauses keepExists ts = x.TransformClauses keepExists ts

    abstract FileExtension : string
    default x.FileExtension = ".smt2"

    abstract Name : string
    default x.Name = "Transformed"

    member x.DirectoryForTransformed directory = directory + "." + x.Name

    abstract CommandsToStrings : transformedCommand list -> string list list
    default x.CommandsToStrings commands = [List.map toString commands]

    member x.CodeTransformation opts commands =
        let chcSystem = SMTcode.toClauses opts.transform opts.tip opts.sync_terms commands
        (x :> ITransformer).TransformClauses opts.keep_exists chcSystem

    member x.SaveClauses directory dst commands =
        let lines = List.collect x.CommandsToStrings commands
        for testIndex, newTest in List.indexed lines do
            let path = Path.ChangeExtension(dst, $".%d{testIndex}%s{x.FileExtension}")
//            let linearityPostfix = if isNonLinearCHCSystem newTest then ".NonLin" else ".Lin"
//            let fullPath = directory + linearityPostfix + cleanPath path
            let fullPath = Path.Join(x.DirectoryForTransformed directory, path)
            Directory.CreateDirectory(Path.GetDirectoryName(fullPath)) |> ignore
            File.WriteAllLines(fullPath, newTest)
        List.length lines

    member x.GenerateClausesSingle (opts : solvingOptions) =
        let outputPath =
            match opts.output with
            | Some outputPath ->
                fun (path : string) -> Path.Join(outputPath, Path.GetFileName(path))
            | None -> id
        let exprs = SMTExpr.parseFile opts.path
        let transformed = x.CodeTransformation opts exprs
        let paths =
            seq {
                let lines = List.collect x.CommandsToStrings transformed
                for testIndex, newTest in List.indexed lines do
                    let path = Path.ChangeExtension(opts.path, $".%s{x.Name}.%d{testIndex}%s{x.FileExtension}")
                    let fullPath = outputPath path
                    File.WriteAllLines(fullPath, newTest)
                    yield fullPath
            } |> List.ofSeq
        paths

let private generateClauses (x : IDirectoryTransformer<string>) (opts : solvingOptions) =
    let referenceDirectory = $"%s{opts.path}.Z3.Z3Answers"
    let shouldCompareResults = false //TODO
    let shouldBeTransformed (src : string) dst =
        let ext = Path.GetExtension(src)
        ext = ".smt2" &&
        (not shouldCompareResults ||
            let referenceFile = Path.ChangeExtension(Path.Join(referenceDirectory, dst), sprintf ".0.smt2")
            File.Exists(referenceFile))
    let mutable files = 0
    let mutable successful = 0
    let mutable total_generated = 0
    let mapFile (src : string) dst =
        if shouldBeTransformed src dst then
            if IN_VERBOSE_MODE () then printfn $"Transforming: %s{src}"
            files <- files + 1
            let exprs = SMTExpr.parseFile src
            try
                if opts.force || not <| isBadBenchmark exprs then
                    let newTests = x.CodeTransformation opts exprs
                    total_generated <- total_generated + x.SaveClauses opts.path dst newTests
                successful <- successful + 1
            with e -> if IN_VERBOSE_MODE () then printfn $"Exception in %s{src}: {e.Message}"
    walk_through opts.path "" mapFile |> ignore
    if IN_VERBOSE_MODE () then printfn $"All files:       %d{files}"
    if IN_VERBOSE_MODE () then printfn $"Successful:      %d{successful}"
    if IN_VERBOSE_MODE () then printfn $"Total generated: %d{total_generated}"
    x.DirectoryForTransformed opts.path

[<AbstractClass>]
type IConcreteTransformer () =
    inherit IDirectoryTransformer<string>()

    override x.GenerateClauses opts = generateClauses x opts

let private sortTransformClauses keepExists chcSystem =
    let noADTSystem = SMTcode.DatatypesToSorts.datatypesToSorts chcSystem
    let set_logic_all = SetLogic "ALL"
    cleanCommands keepExists set_logic_all noADTSystem

let private adtTransformClauses keepExists chcSystem =
    let set_logic_horn = SetLogic "HORN"
    cleanCommands keepExists set_logic_horn chcSystem

type SortHornTransformer () =
    inherit IConcreteTransformer ()
    override x.TransformClauses keepExists chcSystem = sortTransformClauses keepExists chcSystem

type ADTHornTransformer () =
    inherit IConcreteTransformer ()
    override x.TransformClauses keepExists chcSystem = adtTransformClauses keepExists chcSystem

type ISolver =
    inherit ITransformer
    abstract member TransformAndRunOnBenchmark : solvingOptions -> unit
    abstract member Solve : string -> SolverResult

[<AbstractClass>]
type IDirectorySolver<'directory>() =
    inherit IDirectoryTransformer<'directory>()
    let cleanPath (path : string) =
        let newpath = Regex.Replace(path, "[^a-zA-Z0-9_./]", "")
        newpath

    let takeCommandsBeforeFirstCheckSat = List.takeWhile (function Command CheckSat -> false | _ -> true)
    let takeOnlyQueryAcrossAssertsInTIPBenchmark = List.filter (function Assert(Not _) -> true | Assert _ -> false | _ -> true)

    abstract member InterpretResult : string -> string -> SolverResult
    abstract member BinaryName : string
    abstract member BinaryOptions : string -> string
    abstract member RunOnBenchmarkSet : bool -> 'directory -> string
    abstract member RerunSat : 'directory -> string
    default x.RerunSat directory = x.RunOnBenchmarkSet true directory
    abstract member Solve : string -> SolverResult

    member x.SolveWithTime filename =
        if IN_VERBOSE_MODE () then printfn $"Solving %s{filename} with timelimit %d{SECONDS_TIMEOUT} seconds"
        let timer = Stopwatch()
        timer.Start()
        let result = (x :> ISolver).Solve filename
        let time = int timer.ElapsedMilliseconds
        let time = min time (MSECONDS_TIMEOUT ())
        match result with
        | UNKNOWN _ when time = MSECONDS_TIMEOUT () -> TIMELIMIT, time
        | _ -> result, time

    interface ISolver with
        member x.Solve filename = x.Solve filename
        member x.TransformAndRunOnBenchmark opts =
            match () with
            | _ when File.Exists(opts.path) ->
                let outputFiles = x.GenerateClausesSingle opts
                match outputFiles with
                | [] -> printfn "unknown"
                | [outputFile] ->
                    if IN_VERBOSE_MODE () then printfn $"CHC system in %s{opts.path} is preprocessed and saved in %s{outputFile}"
                    let result, time = x.SolveWithTime outputFile
                    if IN_VERBOSE_MODE () then printfn $"Solver run on %s{outputFile} and the result is {result} which was obtained in %d{time} msec."
                    else printfn $"%s{quietModeToString result}"
                | _ ->
                    if IN_VERBOSE_MODE () then printfn $"Preprocessing of %s{opts.path} produced %d{List.length outputFiles} files:"
                    if IN_VERBOSE_MODE () then List.iter (printfn "%s") outputFiles
                    for outputFile in outputFiles do
                        let result, time = x.SolveWithTime outputFile
                        if IN_VERBOSE_MODE () then printfn $"Solver run on %s{outputFile} and the result is {result} which was obtained in %d{time} msec."
            | _ when Directory.Exists(opts.path) ->
                let outputDirectory = x.TransformBenchmarkAndReturn opts
                let resultsDirectory = if opts.rerun then x.RerunSat outputDirectory else x.RunOnBenchmarkSet false outputDirectory
                if IN_VERBOSE_MODE () then printfn $"Solver run on {outputDirectory} and saved results in %s{resultsDirectory}"
            | _ -> failwithf $"There is no such file or directory: %s{opts.path}"

[<AbstractClass>]
type IConcreteSolver () =
    inherit IDirectorySolver<string> ()

    override x.RerunSat directory =
        let shouldRerun dst =
            match Option.map parseResultPair <| ResultTable.rawFileResult dst with
            | Some (_, SAT _) -> true
            | _ -> false
        x.ConditionalRunOnBenchmarkSet shouldRerun directory

    override x.GenerateClauses opts = generateClauses x opts

    member x.AnswersDirectory directory = $"%s{directory}.%s{x.Name}Answers"

    abstract member ShouldSearchForBinaryInEnvironment : bool

    member private x.WorkingDirectory (filename : string) =
        if x.ShouldSearchForBinaryInEnvironment
            then Environment.GetEnvironmentVariable(x.BinaryName)
            else filename
        |> Path.GetDirectoryName

    member private x.SetupProcess (psinfo : ProcessStartInfo) filename =
        let path = ref ""
        psinfo.FileName <- if psinfo.Environment.TryGetValue(x.BinaryName, path) then !path else x.BinaryName
        psinfo.Arguments <- x.BinaryOptions filename
        psinfo.WorkingDirectory <- x.WorkingDirectory filename

    override x.Solve (filename : string) =
        use p = new Process()
        p.StartInfo.RedirectStandardOutput <- true
        p.StartInfo.RedirectStandardError <- true
        p.StartInfo.UseShellExecute <- false
        p.StartInfo.CreateNoWindow <- true
        p.StartInfo.WindowStyle <- ProcessWindowStyle.Hidden
        let error = StringBuilder()
        let output = StringBuilder()
        p.ErrorDataReceived.Add(fun e -> error.AppendLine(e.Data) |> ignore)
        p.OutputDataReceived.Add(fun o -> output.AppendLine(o.Data) |> ignore)
        x.SetupProcess p.StartInfo filename

        p.Start() |> ignore
        p.BeginOutputReadLine()                     // output is read asynchronously
        p.BeginErrorReadLine()                      // error is read asynchronously (if we read both stream synchronously, deadlock is possible
                                                    // see: https://docs.microsoft.com/en-us/dotnet/api/system.diagnostics.processstartinfo.redirectstandardoutput?view=net-5.0#code-try-4
        let exited = p.WaitForExit(MSECONDS_TIMEOUT ())
        p.Close()
        if not exited then
            TIMELIMIT
        else x.InterpretResult (error.ToString().Trim()) (output.ToString().Trim())

    member private x.ConditionalRunOnBenchmarkSet overwrite dir =
        let run_file (src : string) (dst : string) =
            let dst = dir + dst
            Directory.CreateDirectory(Path.GetDirectoryName(dst)) |> ignore
            if Path.GetExtension(src) = x.FileExtension && overwrite dst then
                try
                    if IN_VERBOSE_MODE () then printfn $"Running %s{x.Name} on %s{src}"
                    let answer, time = x.SolveWithTime src
                    File.WriteAllText(dst, $"%d{time},{answer}")
                with e -> if IN_VERBOSE_MODE () then printfn $"Exception in %s{src}: %s{dst}"
            elif IN_VERBOSE_MODE () then printfn $"%s{x.Name} skipping %s{src} (answer exists)"
        walk_through dir $".%s{x.Name}Answers" run_file

    override x.RunOnBenchmarkSet overwrite dir =
        let overwrite dst = overwrite || not <| File.Exists(dst)
        x.ConditionalRunOnBenchmarkSet overwrite dir

type CVC4FiniteSolver () =
    inherit IConcreteSolver ()
    override x.ShouldSearchForBinaryInEnvironment = false
    override x.TransformClauses keepExists chcSystem = sortTransformClauses keepExists chcSystem

    override x.Name = "CVC4Finite"
    override x.BinaryName = "cvc4"
    override x.BinaryOptions filename = $"--finite-model-find --tlimit=%d{MSECONDS_TIMEOUT ()} %s{filename}"

    override x.InterpretResult error raw_output =
        if error <> "" then ERROR(error) else
        let output = Environment.split raw_output
        match output with
        | line::_ when line.StartsWith("(error ") -> ERROR(raw_output)
        | line::_ when line = "sat" -> SAT FiniteModel
        | line::_ when line = "unsat" -> UNSAT
        | line::reason::_ when line = "unknown" && reason = "(:reason-unknown timeout)" -> TIMELIMIT
        | line::reason::_ when line = "unknown" -> UNKNOWN reason
        | _ -> UNKNOWN raw_output

type EldaricaSolver () =
    inherit IConcreteSolver ()
    override x.ShouldSearchForBinaryInEnvironment = true
    override x.TransformClauses keepExists chcSystem = adtTransformClauses keepExists chcSystem

    override x.Name = "Eldarica"
    override x.BinaryName = "eld"
    override x.BinaryOptions filename = $"-horn -hsmt -t:%d{SECONDS_TIMEOUT} %s{filename}"

    override x.InterpretResult error raw_output =
        let output = Environment.split raw_output
        match output with
        | line::_ when line.StartsWith("(error") -> ERROR raw_output
        | line::_ when line = "unknown" -> UNKNOWN raw_output
        | line::_ when line = "sat" -> SAT SizeElemFormula
        | line::_ when line = "unsat" -> UNSAT
        | _ -> UNKNOWN (error + " &&& " + raw_output)

type Z3Solver () =
    inherit IConcreteSolver ()
    override x.ShouldSearchForBinaryInEnvironment = false
    override x.TransformClauses keepExists chcSystem = adtTransformClauses keepExists chcSystem

    override x.Name = "Z3"
    override x.BinaryName = "z3"
    override x.BinaryOptions filename = $"-smt2 -nw -memory:%d{MEMORY_LIMIT_MB} -T:%d{SECONDS_TIMEOUT} %s{filename}"

    override x.InterpretResult error raw_output =
        let output = Environment.split raw_output
        match output with
        | line::_ when line = "timeout" -> TIMELIMIT
        | line::_ when line = "unsat" -> UNSAT
        | line::_ when line = "sat" -> SAT ElemFormula
        | _ when error = "" && raw_output = "" -> OUTOFMEMORY
        | ["unknown"; ""] -> UNKNOWN ""
        | _ -> UNKNOWN (error + " &&& " + raw_output)

type MyZ3Solver () =
    inherit IConcreteSolver ()
    override x.ShouldSearchForBinaryInEnvironment = true
    override x.TransformClauses keepExists chcSystem = adtTransformClauses keepExists chcSystem

    override x.Name = "MyZ3"
    override x.BinaryName = "myz3"
    override x.BinaryOptions filename = $"-v:1 fp.engine=spacer -smt2 -nw -memory:%d{MEMORY_LIMIT_MB} -T:%d{SECONDS_TIMEOUT} %s{filename}"
//    override x.BinaryOptions filename = $"fp.engine=spacer -smt2 -nw -memory:%d{MEMORY_LIMIT_MB} -T:%d{SECONDS_TIMEOUT} %s{filename}"

    override x.InterpretResult error raw_output =
        let raw_output = raw_output.Trim()
        let error = error.Trim()
        let output = Environment.split raw_output
        match output with
        | line::_ when line = "timeout" -> TIMELIMIT
        | line::_ when line = "unsat" -> UNSAT
        | line::_ when line = "sat" -> SAT ElemFormula
        | _ when error = "" && raw_output = "" -> OUTOFMEMORY
        | "unknown"::_ ->
            match Environment.split error with
            | es when List.contains "off-the-shelf solver ended with sat" es -> SAT FiniteModel
            | _ -> UNKNOWN (error + " &&& " + raw_output)
        | _ -> UNKNOWN (error + " &&& " + raw_output)

type CVC4IndSolver () =
    inherit IConcreteSolver ()
    override x.ShouldSearchForBinaryInEnvironment = false
    override x.TransformClauses keepExists chcSystem = adtTransformClauses keepExists chcSystem

    override x.Name = "CVC4Ind"
    override x.BinaryName = "cvc4"
    override x.BinaryOptions filename =
        $"--quant-ind --quant-cf --conjecture-gen --conjecture-gen-per-round=3 --full-saturate-quant --tlimit=%d{MSECONDS_TIMEOUT ()} %s{filename}"

    override x.InterpretResult error raw_output =
        if error <> "" then ERROR(error) else
        let output = Environment.split raw_output
        match output with
        | line::_ when line.StartsWith("(error ") -> ERROR(raw_output)
        | line::_ when line = "sat" -> SAT NoModel
        | line::_ when line = "unsat" -> UNSAT
        | line::reason::_ when line = "unknown" && reason = "(:reason-unknown timeout)" -> TIMELIMIT
        | line::reason::_ when line = "unknown" -> UNKNOWN reason
        | _ -> UNKNOWN raw_output

type VeriMAPiddtSolver () =
    inherit IConcreteSolver ()

    let isRule =
        let rec isRule = function
            | ExistsRule _
            | BaseRule(_, Bot) -> false
            | ForallRule(_, r) -> isRule r
            | BaseRule _ -> true
        function
        | TransformedCommand r -> isRule r
        | _ -> true

    let binaryName = "VeriMAP-iddt"

    override x.ShouldSearchForBinaryInEnvironment = true
    override x.Name = binaryName
    override x.BinaryName = binaryName
    override x.BinaryOptions filename = $"--timeout=%d{SECONDS_TIMEOUT} --check-sat %s{filename}"
    override x.FileExtension = ".pl"
    override x.TransformClauses keepExists chcSystem = adtTransformClauses keepExists chcSystem

    override x.CommandsToStrings commands =
        if PrintToProlog.isFirstOrderPrologProgram commands then [PrintToProlog.toPrologFile commands] else []

    override x.InterpretResult error raw_output =
        if error <> "" then ERROR(error) else
        let output = Environment.split raw_output
        match output with
        | _::line::_ when line.Contains("Answer") && line.EndsWith("true") -> SAT ElemFormula
        | _::line::_ when line.Contains("Answer") && line.EndsWith("false") -> UNSAT
        | _ -> UNKNOWN raw_output

type VampireSolver () =
    inherit IConcreteSolver ()

    let splitModules output =
        let delimiter = "% ------------------------------"
        let f (log, logs) (prev, cur) =
            if prev = delimiter && cur = delimiter then ([], List.rev log::logs) else (prev::log, logs)
        let _, logs = List.fold f ([], []) (List.pairwise output)
        List.rev logs

    let pickTextAfter (line : string) (text : string list) =
        let len = String.length line
        text |> List.pick (fun (s : string) -> let index = s.IndexOf(line) in if index = -1 then None else Some <| s.Substring(index + len))

    let proofOrRefutation moduleOutput =
        let termString = "% Termination reason: "
        let reason = pickTextAfter termString moduleOutput
        match reason with
        | "Satisfiable" ->
            match pickTextAfter "SZS output start " moduleOutput with
            | s when s.StartsWith("Saturation") -> Saturation
            | s when s.StartsWith("FiniteModel") -> FiniteModel
            | _ -> __notImplemented__()
            |> SAT |> Some
        | "Refutation" -> Some UNSAT
        | "Inappropriate"
        | "Memory limit"
        | "Time limit" -> None
        | _ when reason.StartsWith("Refutation not found") -> None
        | _ -> __notImplemented__()

    let interpretResult (output : string list) raw_output =
        match splitModules output |> List.tryPick proofOrRefutation with
        | Some result -> result
        | None -> UNKNOWN raw_output

    override x.ShouldSearchForBinaryInEnvironment = true
    override x.Name = "Vampire"
    override x.BinaryName = "vampire"
    override x.BinaryOptions filename =
        let magic_options = "--mode portfolio --forced_options av=off:newcnf=off:anc=known:sac=off:nicw=off:amm=all:afp=0:aac=ground:afq=1.5:afr=off:add=on:gsaa=off:acc=off:ccuc=all --schedule casc"
        $"""--input_syntax smtlib2 %s{if IN_VERBOSE_MODE () then "" else " --output_mode smtcomp"} {magic_options} --memory_limit {MEMORY_LIMIT_MB} --time_limit {SECONDS_TIMEOUT}s %s{filename}"""
        //TODO: return mode casc_sat: it does not produce meaningful saturation sets as it tries `--newcnf on`, which has a bug (see: https://github.com/vprover/vampire/issues/240)
        //TODO: `-av off` is needed because AVATAR is enabled by default and it also has a bug (with booleans)

    override x.TransformClauses keepExists chcSystem =
        let sortMode = true //TODO: add option?
        let transform, logic = if sortMode then sortTransformClauses, "UF" else adtTransformClauses, "UFDT"
        let chcs = transform keepExists chcSystem
        let setlogic = OriginalCommand <| SetLogic logic
        List.map (List.map (function OriginalCommand (SetLogic _) -> setlogic | c -> c)) chcs

    override x.InterpretResult error raw_output =
        if error <> "" then ERROR(error) else
        let output = Environment.split raw_output
        match output with
        | _ when raw_output = "" -> TIMELIMIT
        | "unknown"::_ -> UNKNOWN ""
        | "sat"::_ -> SAT Saturation
        | "unsat"::_ -> UNSAT
        | _ -> interpretResult output raw_output

type AllSolver () =
    inherit IDirectorySolver<string list>()
    let solvers : IConcreteSolver list = [Z3Solver(); EldaricaSolver(); CVC4IndSolver(); CVC4FiniteSolver(); VeriMAPiddtSolver(); VampireSolver()]

    override x.Name = "AllSolvers"
    override x.BinaryName = "AllSolvers"
    override x.BinaryOptions _ = __unreachable__()
    override x.InterpretResult _ _ = __unreachable__()
    override x.TransformClauses _ _ = __unreachable__()

    override x.Solve filename =
        for solver in solvers do (solver :> ISolver).Solve(filename) |> ignore
        UNKNOWN "All solvers"

    override x.GenerateClauses opts =
        let forceGenerateClauses (solver : IConcreteSolver) =
            if IN_VERBOSE_MODE () then printfn $"Generating clauses for %s{solver.Name}"
            solver.GenerateClauses {opts with force = false}
        let paths =
            if opts.force
                then solvers |> List.map forceGenerateClauses
                else solvers |> List.map (fun solver -> solver.DirectoryForTransformed opts.path)
        paths

    override x.RunOnBenchmarkSet overwrite runs =
        let results =
            if overwrite
                then List.map2 (fun (solver : IConcreteSolver) path -> solver.RunOnBenchmarkSet false path) solvers runs
                else List.map2 (fun (solver : IConcreteSolver) path -> solver.AnswersDirectory path) solvers runs
        let names = solvers |> List.map (fun solver -> solver.Name)
        let exts = solvers |> List.map (fun solver -> solver.FileExtension)
        let directory = ResultTable.GenerateReadableResultTable names exts results
        if IN_VERBOSE_MODE () then printfn "LaTeX table: %s" <| ResultTable.GenerateLaTeXResultTable names exts results
        directory
