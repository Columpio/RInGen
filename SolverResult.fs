module RInGen.SolverResult


let mutable SECONDS_TIMEOUT = 5 * 60
let MSECONDS_TIMEOUT () = SECONDS_TIMEOUT * 1000
let MEMORY_LIMIT_MB = 12 * 1024

type SolverResult = SAT | UNSAT | ERROR of string | UNKNOWN of string | TIMELIMIT | OUTOFMEMORY

let quietModeToString = function
    | SAT -> "sat"
    | UNSAT -> "unsat"
    | _ -> "unknown"

let parseSolverResult s =
    match () with
    | _ when s = "SAT" -> SAT
    | _ when s = "UNSAT" -> UNSAT
    | _ when s = "ERROR" -> ERROR ""
    | _ when s = "UNKNOWN" -> UNKNOWN ""
    | _ when s = "TIMELIMIT" -> TIMELIMIT
    | _ when s = "OUTOFMEMORY" -> OUTOFMEMORY
    | _ -> __notImplemented__()

let parseResultPair = function
    | Some (time : string, answer) -> Some (int time, parseSolverResult answer)
    | None -> None
