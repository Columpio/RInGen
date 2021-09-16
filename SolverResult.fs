module RInGen.SolverResult

type Model = ElemFormula | SizeElemFormula | FiniteModel | Saturation | NoModel
type SolverResult =
    | SAT of Model | UNSAT of string | ERROR of string | UNKNOWN of string | SOLVER_TIMELIMIT | OUTOFMEMORY
    override x.ToString() =
        match x with
        | SAT m -> $"SAT %O{m}"
        | UNSAT refutation -> $"UNSAT\n{refutation}"
        | SOLVER_TIMELIMIT -> "SOLVER_TIMELIMIT"
        | OUTOFMEMORY -> "OUTOFMEMORY"
        | ERROR s -> $"ERROR %s{s}"
        | UNKNOWN s -> $"UNKNOWN %s{s}"

let compactStatus = function
    | ERROR _ -> ERROR ""
    | UNKNOWN _ -> UNKNOWN ""
    | r -> r

let quietModeToString = function
    | SAT _ -> "sat"
    | UNSAT _ -> "unsat"
    | _ -> "unknown"

let tryParseSolverResult (s : string) =
    let s = s.Trim()
    match split " " s with
    | "SAT":: model ->
        match model with
        | ["ElemFormula"] -> SAT ElemFormula
        | ["SizeElemFormula"] -> SAT SizeElemFormula
        | ["FiniteModel"] -> SAT FiniteModel
        | ["Saturation"] -> SAT Saturation
        | _ -> SAT NoModel
        |> Some
    | "UNSAT"::_ -> UNSAT "" |> Some
    | "ERROR"::reason -> ERROR (join " " reason) |> Some
    | "UNKNOWN"::reason -> UNKNOWN (join " " reason) |> Some
    | "SOLVER_TIMELIMIT"::_ -> SOLVER_TIMELIMIT |> Some
    | "OUTOFMEMORY"::_ -> OUTOFMEMORY |> Some
    | _ -> None

let parseSolverResult s =
    match tryParseSolverResult s with
    | Some res -> res
    | None -> __notImplemented__()
