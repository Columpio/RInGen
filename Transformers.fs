module RInGen.Transformers
open System
open System.IO
open Programs

type TransformationFail =
    | TRANS_TIMELIMIT
    | TRANS_MEMORYLIMIT
    | TRANS_HIGH_ORDER_PROBLEM
    | TRANS_CONTAINS_EXISTENTIALS
    | TRANS_UNHANDLED_EXCEPTION

let tryParseTransformationFail (s : string) =
    let s = s.Trim()
    match s with
    | "TRANS_TIMELIMIT" -> Some TRANS_TIMELIMIT
    | "TRANS_HIGH_ORDER_PROBLEM" -> Some TRANS_HIGH_ORDER_PROBLEM
    | "TRANS_CONTAINS_EXISTENTIALS" -> Some TRANS_CONTAINS_EXISTENTIALS
    | "TRANS_UNHANDLED_EXCEPTION" -> Some TRANS_UNHANDLED_EXCEPTION
    | _ -> None

type RunConfig =
    InteractiveRun | PathRun of path
    override x.ToString() =
        match x with
        | InteractiveRun -> "*interactive input*"
        | PathRun path -> path

[<AbstractClass>]
type TransformerProgram (options : transformOptions) =
    inherit Program()

    let isHighOrderBenchmark cmnds =
        let hasDefines = List.exists (function Definition _ -> true | _ -> false) cmnds
        let hasDeclareFuns = List.exists (function Command (DeclareFun _) -> true | _ -> false) cmnds
        hasDefines && hasDeclareFuns

    let tryFindExistentialClauses =
        let tryFindExistentialClauses = function
            | TransformedCommand(Rule(qs, _, _) as r) when Quantifiers.existsp (function ExistsQuantifier _ -> true | _ -> false) qs -> Some r
            | _ -> None
        List.tryPick tryFindExistentialClauses

    abstract Transform : transformContext -> string list

    static member FailInfoFileExtension = ".transformation_info"

    member private x.ReportTransformationProblem dstPath (problem : TransformationFail) message =
        let dstPath = Path.ChangeExtension(dstPath, TransformerProgram.FailInfoFileExtension)
        File.WriteAllText(dstPath, toString problem)
        print_warn_verbose message
        false

    member private x.ReportTimelimit srcPath dstPath =
        x.ReportTransformationProblem dstPath TRANS_TIMELIMIT $"Transformation of %s{srcPath} halted due to a timelimit"

    member private x.ParseAndTransform (srcPath : string) dstPath =
        let exprs = SMTExpr.Parser().ParseFile srcPath
        x.PerformTransform (PathRun srcPath) exprs dstPath

    member x.PerformTransform (srcPath : RunConfig) exprs dstPath =
//        let mutable files = 0
//        let mutable successful = 0
//        let mutable total_generated = 0
//                files <- files + 1
        if isHighOrderBenchmark exprs then x.ReportTransformationProblem dstPath TRANS_HIGH_ORDER_PROBLEM $"%O{srcPath} will not be transformed as it has a mix of define-fun and declare-fun commands" else
        try
            let trCtx = ClauseTransform.toClauses options exprs
            match tryFindExistentialClauses trCtx.commands with
            | Some r -> x.ReportTransformationProblem dstPath TRANS_CONTAINS_EXISTENTIALS $"Transformed %s{dstPath} contains existential subclause: %O{r}"
            | None ->
            let transformedProgram = x.Transform trCtx
            Program.SaveFile dstPath transformedProgram
            true
//            total_generated <- total_generated + x.SaveClauses opts.path dst newTests
//            successful <- successful + 1
        with
        | :? OutOfMemoryException -> x.ReportTransformationProblem dstPath TRANS_MEMORYLIMIT $"Transformation of %O{srcPath} halted due to a memory limit"
        | e -> x.ReportTransformationProblem dstPath TRANS_UNHANDLED_EXCEPTION $"Exception in %O{srcPath}: {e.Message}"
//        if IN_VERBOSE_MODE () then printfn $"All files:       %d{files}"
//        if IN_VERBOSE_MODE () then printfn $"Successful:      %d{successful}"
//        if IN_VERBOSE_MODE () then printfn $"Total generated: %d{total_generated}"

    override x.RunOnFile srcPath dstPath =
        match options.child_transformer with
        | None ->
            print_verbose $"Transforming: %s{srcPath}"
            let task = Async.AwaitTask(Async.StartAsTask(async { return x.ParseAndTransform srcPath dstPath }), MSECONDS_TIMEOUT ()) //TODO transformation time should count in total run
            match Async.RunSynchronously task with
            | None -> x.ReportTimelimit srcPath dstPath
            | Some result -> result
        | Some transformer -> transformer.RunOnFile srcPath dstPath

let private preambulizeCommands logic chcSystem =
    OriginalCommand(SetLogic logic) :: chcSystem @ [OriginalCommand CheckSat]

type OriginalTransformerProgram (options) =
    inherit TransformerProgram(options)

    override x.TargetPath path = $"%s{path}.Original"

    override x.Transform trCtx =
        let commands' = preambulizeCommands "HORN" trCtx.commands
        List.map toString commands'

type RCHCTransformerProgram (options) =
    inherit TransformerProgram(options)

    let toString = function
        | TransformedCommand(Rule(qs, body, Bot)) ->
            match body with
            | [] -> $"{Bot}"
            | [y] -> $"(not {y})"
            | _ -> $"""(not (and {body |> List.filter ((<>) Top) |> List.map toString |> join "\n\t\t\t"}))"""
            |> Quantifiers.toString qs
            |> sprintf "(assert %s)"
        | c -> toString c

    override x.TargetPath path = $"%s{path}.RCHC_Transform"

    override x.Transform trCtx =
        let commands' = preambulizeCommands "HORN" trCtx.commands
        List.map toString commands'

type FreeSortsTransformerProgram (options) =
    inherit TransformerProgram(options)

    override x.TargetPath path = $"%s{path}.FreeSorts"

    override x.Transform trCtx =
        let noADTSystem = ClauseTransform.DatatypesToSorts.datatypesToSorts trCtx.commands
        let commands = preambulizeCommands "UF" noADTSystem
        let commands = ClauseTransform.SubstituteLemmas.substituteLemmas commands
        let commands = Simplification.simplify trCtx.diseqs commands
        List.map toString commands

type PrologTransformerProgram (options) =
    inherit TransformerProgram(options)

    override x.TargetPath path = $"%s{path}.Prolog"

    override x.FileExtension = ".pl"

    override x.Transform trCtx =
        let commands = preambulizeCommands "HORN" trCtx.commands
        if PrintToProlog.isFirstOrderPrologProgram commands
            then PrintToProlog.toPrologFile commands
            else failwith_verbose "not a first order Prolog program"
