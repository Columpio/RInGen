module RInGen.SolverResult

type Model = ElemFormula | SizeElemFormula | FiniteModel | Saturation | NoModel
type SolverResult = SAT of Model | UNSAT | ERROR of string | UNKNOWN of string | TIMELIMIT | OUTOFMEMORY

let onlyStatus = function
    | SAT _ -> "SAT"
    | UNSAT -> "UNSAT"
    | ERROR _ -> "ERROR"
    | UNKNOWN _ -> "UNKNOWN"
    | TIMELIMIT -> "TIMELIMIT"
    | OUTOFMEMORY -> "OUTOFMEMORY"

let quietModeToString = function
    | SAT _ -> "sat"
    | UNSAT -> "unsat"
    | _ -> "unknown"

let isSAT = function SAT _ -> true | _ -> false
let isUNSAT = function UNSAT -> true | _ -> false
let isERROR = function ERROR _ -> true | _ -> false
let isUNKNOWN = function UNKNOWN _ -> true | _ -> false
let isTIMELIMIT = function TIMELIMIT -> true | _ -> false
let isOUTOFMEMORY = function OUTOFMEMORY -> true | _ -> false

let private tryParseSolverResult s =
    match split " " s with
    | "SAT":: model ->
        match model with
        | ["ElemFormula"] -> SAT ElemFormula
        | ["SizeElemFormula"] -> SAT SizeElemFormula
        | ["FiniteModel"] -> SAT FiniteModel
        | ["Saturation"] -> SAT Saturation
        | _ -> SAT NoModel
        |> Some
    | "UNSAT"::_ -> UNSAT |> Some
    | "ERROR"::reason -> ERROR (join " " reason) |> Some
    | "UNKNOWN"::reason -> UNKNOWN (join " " reason) |> Some
    | "TIMELIMIT"::_ -> TIMELIMIT |> Some
    | "OUTOFMEMORY"::_ -> OUTOFMEMORY |> Some
    | _ -> None

let parseSolverResult s =
    match tryParseSolverResult s with
    | Some res -> res
    | None -> __notImplemented__()

let parseResultPair (time : string, answer) =
    match Int32.TryParse time, tryParseSolverResult answer with
    | Some time, Some answer -> Some (time, answer)
    | _ -> None
