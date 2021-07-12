module RInGen.SolverResult


let mutable SECONDS_TIMEOUT = 5 * 60
let MSECONDS_TIMEOUT () = SECONDS_TIMEOUT * 1000
let MEMORY_LIMIT_MB = 12 * 1024

type Model = ElemFormula | SizeElemFormula | FiniteModel | Saturation | NoModel
type SolverResult = SAT of Model | UNSAT | ERROR of string | UNKNOWN of string | TIMELIMIT | OUTOFMEMORY

let quietModeToString = function
    | SAT _ -> "sat"
    | UNSAT -> "unsat"
    | _ -> "unknown"

let parseSolverResult s =
    match split " " s with
    | "SAT":: model ->
        match model with
        | ["ElemFormula"] -> SAT ElemFormula
        | ["SizeElemFormula"] -> SAT SizeElemFormula
        | ["FiniteModel"] -> SAT FiniteModel
        | ["Saturation"] -> SAT Saturation
        | _ -> SAT NoModel
    | "UNSAT"::_ -> UNSAT
    | "ERROR"::reason -> ERROR (join " " reason)
    | "UNKNOWN"::reason -> UNKNOWN (join " " reason)
    | "TIMELIMIT"::_ -> TIMELIMIT
    | "OUTOFMEMORY"::_ -> OUTOFMEMORY
    | _ -> __notImplemented__()

let parseResultPair = function
    | Some (time : string, answer) -> Some (int time, parseSolverResult answer)
    | None -> None
