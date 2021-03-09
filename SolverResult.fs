module FLispy.SolverResult

open System.IO
open System.Text.RegularExpressions


let mutable SECONDS_TIMEOUT = 5 * 60
let MSECONDS_TIMEOUT () = SECONDS_TIMEOUT * 1000
let MEMORY_LIMIT_MB = 12 * 1024

type SolverResult = SAT of string | UNSAT | ERROR of string | UNKNOWN of string | TIMELIMIT | OUTOFMEMORY
let parseSolverResult s =
    match () with
    | _ when s = "SAT" -> SAT ""
    | _ when s = "UNSAT" -> UNSAT
    | _ when s = "ERROR" -> ERROR ""
    | _ when s = "UNKNOWN" -> UNKNOWN ""
    | _ when s = "TIMELIMIT" -> TIMELIMIT
    | _ when s = "OUTOFMEMORY" -> OUTOFMEMORY
    | _ -> __notImplemented__()

let private resultRegex = Regex @"(\d+),(\w+)"
let parseAnswerFile resultFileName =
    let result = resultRegex.Match(File.ReadAllLines(resultFileName).[0]).Groups
    let time = int <| result.[1].Value
    let answer = result.[2].Value
    time, answer
