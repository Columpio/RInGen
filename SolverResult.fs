module RInGen.SolverResult
open FiniteModels

type Model =
    | ElemFormula | SizeElemFormula | FiniteModel of finModel | Saturation of string | NoModel
    override x.ToString() =
        let toStringHeadAndBody head s =
            let body = if s = null || s = "" then "" else "\n" + s
            head + body
        match x with
        | ElemFormula -> "ElemFormula"
        | SizeElemFormula -> "SizeElemFormula"
        | FiniteModel _ -> "FiniteModel"
        | Saturation s -> toStringHeadAndBody "Saturation" s
        | NoModel -> "NoModel"
type SolverResult =
    | SAT of Model | UNSAT of string | ERROR of string | UNKNOWN of string | SOLVER_TIMELIMIT | OUTOFMEMORY
    override x.ToString() =
        match x with
        | SAT m -> $"SAT %O{m}"
        | UNSAT "" -> "UNSAT"
        | UNSAT refutation -> $"UNSAT\n{refutation}"
        | SOLVER_TIMELIMIT -> "SOLVER_TIMELIMIT"
        | OUTOFMEMORY -> "OUTOFMEMORY"
        | ERROR s -> $"ERROR %s{s}"
        | UNKNOWN s -> $"UNKNOWN %s{s}"

let compactStatus = function
    | ERROR _ -> ERROR ""
    | UNKNOWN _ -> UNKNOWN ""
    | UNSAT _ -> UNSAT ""
    | r -> r

let quietModeToString = function
    | SAT _ -> "sat"
    | UNSAT _ -> "unsat"
    | _ -> "unknown"

let tryParseSolverResult (s : string) =
    let s = s.Trim()
    match split " \n" s with
    | "SAT":: model ->
        match model with
        | "ElemFormula"::_ -> SAT ElemFormula
        | "SizeElemFormula"::_ -> SAT SizeElemFormula
        | "FiniteModel"::_ -> SAT (FiniteModel SomeFiniteModel)
        | "Saturation"::_ -> SAT (Saturation "")
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
