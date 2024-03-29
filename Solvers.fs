module RInGen.Solvers
open SMTLIB2
open System.Collections.Generic
open System.IO
open System.Text.RegularExpressions
open System.Threading.Tasks
open RInGen.SolverResult
open Programs
open RInGen.Transformers

[<AbstractClass>]
type SolverProgramRunner () =
    inherit ProgramRunner()

    abstract Name : string
    abstract InterpretResult : string -> string -> SolverResult

    static member PrintResult(result) =
        if IN_EXTRA_VERBOSE_MODE () then printfn $"Solver obtained result: {result}"
        elif IN_QUIET_MODE () then printfn $"{quietModeToString result}"

    member x.AddResultsToTable originalDirectory transDirectory resultsDirectory =
        let tablePath = Path.ChangeExtension(originalDirectory, ".csv")
        if File.Exists(tablePath) then ResultTable.AddResultsToTable tablePath x.Name transDirectory resultsDirectory
        else ResultTable.GenerateReadableResultTable originalDirectory [x.Name] [x.FileExtension] [transDirectory, resultsDirectory]

    override x.RunOnFile srcPath dstPath =
        if File.Exists(dstPath) then print_verbose $"%s{x.Name} skipping %s{srcPath} (answer exists)"; true else
        try
            let statisticsFile, hasFinished, error, output = x.RunProcessOn srcPath
            let result = if hasFinished then x.InterpretResult error output else SOLVER_TIMELIMIT
            let realResult = Statistics.report dstPath srcPath statisticsFile result
            SolverProgramRunner.PrintResult(realResult)
            true
        with e -> print_verbose $"Exception in %s{srcPath}:\n{e}"; false

type CVCFiniteSolver () =
    inherit SolverProgramRunner ()

    override x.ShouldSearchForBinaryInEnvironment = true
    override x.Name = "CVC_FMF"
    override x.BinaryName = "cvc"
    override x.BinaryOptions filename = $"--finite-model-find --produce-models --tlimit=%d{MSECONDS_TIMEOUT ()} %s{filename}"

    override x.InterpretResult error raw_output =
        match error with
        | _ when error.EndsWith("interrupted by timeout.") -> SOLVER_TIMELIMIT
        | _ when error <> "" -> ERROR(error)
        | _ ->
        let output = Environment.split raw_output
        match output with
        | line::_ when line.StartsWith("(error ") -> ERROR(raw_output)
        | line::rawModel when line = "sat" -> FiniteModels.SomeFiniteModel |> FiniteModel |> SAT //TODO: temporary disabled as unstable: FiniteModels.parseCVC rawModel
        | line::_ when line = "unsat" -> UNSAT ""
        | line::reason::_ when line = "unknown" && reason = "(:reason-unknown timeout)" -> SOLVER_TIMELIMIT
        | line::reason::_ when line = "unknown" -> UNKNOWN reason
        | _ -> UNKNOWN raw_output

type EldaricaSolver () =
    inherit SolverProgramRunner ()

    override x.ShouldSearchForBinaryInEnvironment = true
    override x.Name = "Eldarica"
    override x.BinaryName = "eld"
    override x.BinaryOptions filename = $"-horn -hsmt -t:%d{SECONDS_TIMEOUT} %s{filename}"

    override x.InterpretResult error raw_output =
        let output = Environment.split raw_output
        match output with
        | line::_ when line.StartsWith("(error") -> ERROR raw_output
        | line::_ when line = "unknown" -> UNKNOWN raw_output
        | line::_ when line = "sat" -> SAT SizeElemFormula
        | line::_ when line = "unsat" -> UNSAT ""
        | _ -> UNKNOWN (error + " &&& " + raw_output)

type RCHCSolver () =
    inherit SolverProgramRunner ()

    override x.ShouldSearchForBinaryInEnvironment = false
    override x.Name = "RCHC"
    override x.BinaryName = "rchc"
    override x.BinaryOptions filename = filename

    override x.InterpretResult error raw_output =
        let output = Environment.split raw_output
        match output with
        | line::_ when line = "sat" -> SAT(FiniteModel FiniteModels.SomeFiniteModel)
        | line::_ when line = "unsat" -> UNSAT ""
        | _ -> UNKNOWN (error + " &&& " + raw_output)

type Z3Solver () =
    inherit SolverProgramRunner ()

    override x.ShouldSearchForBinaryInEnvironment = false
    override x.Name = "Z3"
    override x.BinaryName = "z3"
    override x.BinaryOptions filename = $"-smt2 -nw -memory:%d{MEMORY_LIMIT_MB} -T:%d{SECONDS_TIMEOUT} %s{filename}"

    override x.InterpretResult error raw_output =
        let output = Environment.split raw_output
        match output with
        | line::_ when line = "timeout" -> SOLVER_TIMELIMIT
        | line::_ when line = "unsat" -> UNSAT ""
        | line::_ when line = "sat" -> SAT ElemFormula
        | _ when error = "" && raw_output = "" -> OUTOFMEMORY
        | ["unknown"; ""] -> UNKNOWN ""
        | _ -> UNKNOWN (error + " &&& " + raw_output)

type MyZ3Solver () =
    inherit SolverProgramRunner ()

    override x.ShouldSearchForBinaryInEnvironment = true
    override x.Name = "MyZ3"
    override x.BinaryName = "myz3"
    override x.BinaryOptions filename = $"-v:1 fp.engine=spacer -smt2 -nw -memory:%d{MEMORY_LIMIT_MB} -T:%d{SECONDS_TIMEOUT} %s{filename}"

    override x.InterpretResult error raw_output =
        let output = Environment.split raw_output
        match output with
        | line::_ when line = "timeout" -> SOLVER_TIMELIMIT
        | line::_ when line = "unsat" -> UNSAT ""
        | line::_ when line = "sat" -> SAT ElemFormula
        | _ when error = "" && raw_output = "" -> OUTOFMEMORY
        | "unknown"::_ ->
            let lines = Environment.split error
            let otsResult = lines |> List.tryPick (fun s -> let a = s.Split("off-the-shelf solver ended with ") in if a.Length > 1 then Some a.[1] else None)
            match otsResult with
            | Some message ->
                if message.StartsWith("sat")
                    then SAT(FiniteModel FiniteModels.SomeFiniteModel)
                elif message.StartsWith("unsat")
                    then UNSAT ""
                else UNKNOWN (error + " &&& " + raw_output)
            | None -> UNKNOWN (error + " &&& " + raw_output)
        | _ -> UNKNOWN (error + " &&& " + raw_output)

type CVC4IndSolver () =
    inherit SolverProgramRunner ()

    override x.ShouldSearchForBinaryInEnvironment = false
    override x.Name = "CVC_Ind"
    override x.BinaryName = "cvc4"
    override x.BinaryOptions filename =
        $"--quant-ind --quant-cf --conjecture-gen --conjecture-gen-per-round=3 --full-saturate-quant --tlimit=%d{MSECONDS_TIMEOUT ()} %s{filename}"

    override x.InterpretResult error raw_output =
        if error <> "" then ERROR(error) else
        let output = Environment.split raw_output
        match output with
        | line::_ when line.StartsWith("(error ") -> ERROR(raw_output)
        | line::_ when line = "sat" -> SAT NoModel
        | line::_ when line = "unsat" -> UNSAT ""
        | line::reason::_ when line = "unknown" && reason = "(:reason-unknown timeout)" -> SOLVER_TIMELIMIT
        | line::reason::_ when line = "unknown" -> UNKNOWN reason
        | _ -> UNKNOWN raw_output

type VeriMAPiddtSolver () =
    inherit SolverProgramRunner ()

    let binaryName = "VeriMAP-iddt"
    override x.ShouldSearchForBinaryInEnvironment = true
    override x.Name = binaryName
    override x.BinaryName = binaryName
    override x.BinaryOptions filename = $"--timeout=%d{SECONDS_TIMEOUT} --check-sat %s{filename}"
    override x.FileExtension = ".pl"

    override x.InterpretResult error raw_output =
        if error <> "" then ERROR(error) else
        let output = Environment.split raw_output
        match output with
        | _::line::_ when line.Contains("Answer") && line.EndsWith("true") -> SAT ElemFormula
        | _::line::_ when line.Contains("Answer") && line.EndsWith("false") -> UNSAT ""
        | _ -> UNKNOWN raw_output

type private refutationSource = Axiom | Inference of string * string list

type VampireSolver () =
    inherit SolverProgramRunner ()

    let mode = "--mode chccomp"

    let splitModules output =
        let reDelimiter = Regex("^(% )?[-]+$")
        let isDelimiter s = reDelimiter.Match(s).Success
        let f (log, logs) (prev, cur) =
            if isDelimiter prev && isDelimiter cur then ([], List.rev log::logs) else (prev::log, logs)
        let _, logs = List.fold f ([], []) (List.pairwise output)
        List.rev logs

    let pickTextAfter (line : string) (text : string list) =
        let len = String.length line
        text |> List.pick (fun (s : string) -> let index = s.IndexOf(line) in if index = -1 then None else Some <| s.Substring(index + len))

    let tffRegex = Regex("([a-zA-Z0-9]+),([^,]+),\((.*)\),(.*)")
    let tffInferenceRegex = Regex("inference\(([a-zA-Z0-9_]+),\[(.*)\],\[(.*)\]\)")

    let regexGroups (m : Match) = m.Groups |> List.ofSeq |> List.map (fun g -> g.Value.Trim()) |> List.tail

    let parseTFF (line : string) =
        let m = tffRegex.Match(line)
        if not m.Success then None else
        match regexGroups m with
        | name::kind::clause::source::_ ->
            let source =
                if kind = "axiom" || source.StartsWith("introduced") then Some Axiom
                elif kind = "plain" then
                    let m = tffInferenceRegex.Match(source)
                    if m.Success then
                        match regexGroups m with
                        | inferenceName::inferenceArgs::inferenceFrom::_ -> Some <| Inference(inferenceName, split "," inferenceFrom)
                        | _ -> __notImplemented__()
                    else None
                else __notImplemented__()
            match source with
            | Some source -> Some(name, (clause, source))
            | None -> None
        | _ -> __notImplemented__()

    let treeHeight refutationTree =
        let rec iter node =
            match snd <| Map.find node refutationTree with
            | Axiom -> 0
            | Inference(kind, children) ->
                let childHeight = List.fold (fun mx child -> max mx (iter child)) 0 children
                let inferenceHeight =
                    match kind with
                    | _ when kind.StartsWith("avatar_") -> 0        // meta variables stuff
                    | _ when kind.EndsWith("_transformation") -> 0  // cnf, ennf and stuff
                    | "rectify"                                     // just reorders quantifiers
                    | "equality_resolution"                         // x = t /\ p(x) -> q(x) ~> p(t) -> q(t)
                    | "flattening" -> 0                             // propagates negation
                    | "resolution"
                    | "subsumption_resolution" -> 1
                    | _ -> __notImplemented__()
                inferenceHeight + childHeight
        let start = Map.pick (fun node (clause, _) -> if clause = "$false" then Some node else None) refutationTree
        iter start

    let rebuildRefutation refutation0 =
        let refutation1 = join "" refutation0
        let refutation2 = refutation1.Split(").tff(") |> List.ofArray
        let refutation3 = List.choose parseTFF refutation2
        let refutationTree = Map.ofList refutation3
        let height = treeHeight refutationTree
        join "\n" refutation0

    let findConfiguration moduleOutput = List.find (fun (s : string) -> s.StartsWith("% ") && String.hasLetters s) moduleOutput

    let proofOrRefutation moduleOutput =
        let termString = "% Termination reason: "
        let reason = pickTextAfter termString moduleOutput
        let configuration = findConfiguration moduleOutput
        match reason with
        | "Satisfiable" ->
            match pickTextAfter "SZS output start " moduleOutput with
            | s when s.StartsWith("Saturation") -> Saturation configuration
            | s when s.StartsWith("FiniteModel") -> FiniteModel FiniteModels.SomeFiniteModel
            | s -> failwith $"Unknown Vampire model type: {s}"
            |> SAT |> Some
        | "Refutation" ->
            let refutationAndGarbage = moduleOutput |> List.skipWhile (fun line -> not <| line.Contains("SZS output start")) |> List.tail
            let refutation = refutationAndGarbage |> List.takeWhile (fun line -> not <| line.Contains("SZS output end"))
            Some (UNSAT <| join "\n" (configuration :: refutation)) //TODO: rebuildRefutation refutation
        | _ -> None

    let splitParallelRun (output : string list) =
        let procIdRegex = Regex("% \((?<procId>\d+)\)")
        let splitByProcessId (line : string) =
            let gs = procIdRegex.Matches(line) |> List.ofSeq |> List.map (fun m -> m.Groups.["procId"])
            let rs = gs |> List.map (fun g -> int(g.Value), g.Index-3, g.Index + g.Length+1)
            let debug = rs |> List.map (fun (_, i, l) -> line.Substring(i, l-i))
            if List.isEmpty rs then [None, line] else
            let ss, _ = List.mapFoldBack (fun (v, ms, me) sen -> (Some v, "% " + line.Substring(me, sen-me)), ms) rs line.Length
            ss
        let iOptOutput = List.collect splitByProcessId output
        let chooseProc lastProc (curProc, s) =
            match curProc with
            | Some curProc -> (curProc, s), curProc
            | None -> (lastProc, s), lastProc
        let iOutput, _ = List.mapFold chooseProc 0 iOptOutput
        let runs = Dictionary<_, _>()
        for i, s in iOutput do
            match Dictionary.tryFind i runs with
            | Some lines -> runs.[i] <- (s::lines)
            | None -> runs.Add(i, [s])
        let plainRuns = runs |> Dictionary.toList |> List.collect (snd >> List.rev)
        plainRuns

    let interpretResult (output : string list) raw_output error =
        let outputSequential = splitParallelRun output
        let outputSplit = splitModules outputSequential
        match List.tryPick proofOrRefutation outputSplit with
        | Some result -> result
        | None -> if error <> "" then ERROR(error) elif raw_output = "" then SOLVER_TIMELIMIT else UNKNOWN raw_output

    override x.ShouldSearchForBinaryInEnvironment = true
    override x.Name = "Vampire"
    override x.BinaryName = "vampire"
    override x.BinaryOptions filename =
        $"""{mode} --input_syntax smtlib2 --memory_limit {MEMORY_LIMIT_MB} --time_limit {SECONDS_TIMEOUT}s %s{filename}"""

    override x.InterpretResult error raw_output =
        let output = Environment.split raw_output
        let output = List.filter (fun (line : string) -> not <| line.Contains("% Warning:")) output
        match output with
        | "unknown"::_ -> UNKNOWN ""
        | "sat"::_ -> SAT (Saturation "")
        | "unsat"::_ -> UNSAT ""
        | _ -> interpretResult output raw_output error

type PortfolioSolver(transformersAndSolvers : (TransformerProgram * SolverProgramRunner) list) =
    inherit Program()

    override x.RunOnFile _ _ = __unreachable__()

    override x.Run path outputPath =
        let inputs =
            transformersAndSolvers
            |> List.map (fun (transformer, solver) -> transformer.Run path outputPath, solver)
        let task =
            inputs
            |> List.map (fun (input, solver) -> Task.Factory.StartNew(fun () -> Option.bind (fun input -> solver.Run input outputPath) input))
            |> Task.WhenAny
        let success = task.Wait(MSECONDS_TIMEOUT_WITH_DELAY ())
        if not success then None else
        let result = task.Result.Result
        result
