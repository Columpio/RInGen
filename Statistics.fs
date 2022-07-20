module RInGen.Statistics
open SMTLIB2
open System.IO
open System.Text.RegularExpressions
open RInGen.SolverResult
open RInGen.Transformers

let private readFileWhenNonEmpty (filename : path) =
    let file = FileInfo(filename)
    if file.Length = 0L then
        System.Threading.Thread.Sleep(10) // result may be unavailible
        file.Refresh()
    if file.Length = 0L then None else Some <| file.OpenRead()

let private readTMPStatFile (timeStatisticsFile : path) =
    let regex = Regex("^(\d+),(\d+.\d+)$")
    match readFileWhenNonEmpty timeStatisticsFile with
    | None -> -1, -1
    | Some file ->
    use statStream = new StreamReader(file)
    let lines = statStream.ReadToEnd() |> Environment.split
    let memory, time = lines |> List.pick (fun line -> let m = regex.Match(line) in if m.Success then Some(m.Groups.[1].Value, m.Groups.[2].Value) else None)
    let memory = int memory                  // kilobytes
    let time = int (1000.0 * (float time))   // milliseconds
    memory, time

type statistics = {
    transformedFileSize: int64  // in kilobytes
    solverRunMemory: int        // in kilobytes
    solverRunTime: int          // in milliseconds
    solverResult: SolverResult
}
type status = TransformationStatus of TransformationFail | SolvingStatus of statistics
let fieldNames = ["TransformedFileSize"; "SolverRunMemory"; "SolverRunTime"; "Status"]
let statisticsCount = List.length fieldNames

let private toStringList (stat : statistics) =
    [
        toString stat.transformedFileSize
        toString stat.solverRunMemory
        toString stat.solverRunTime
        toString stat.solverResult
    ]

let mapResult f = function
    | SolvingStatus stat -> SolvingStatus {stat with solverResult = f stat.solverResult}
    | c -> c

let iterExceptLast doForLast doForRest =
    for _ in 1..statisticsCount-1 do
        doForRest ()
    doForLast ()

let iterTry action = function
    | Some (TransformationStatus status) -> iterExceptLast (fun () -> action <| toString status) (fun () -> action "")
    | Some (SolvingStatus stat) -> stat |> toStringList |> List.iter action
    | None -> iterExceptLast (fun () -> action "") (fun () -> action "")

let private writeStatistics (path : path) (stat : statistics) =
    let contents = toStringList stat
    File.WriteAllLines(path, contents)

let private tryReadStatisticsFromList = function
    | [tfs; srm; srt; sr] ->
        match tryParseTransformationFail sr with
        | Some transInfo -> transInfo |> TransformationStatus |> Some
        | None ->
            opt {
                let! transformedFileSize = Int64.TryParse tfs
                let! solverRunMemory = Int32.TryParse srm
                let! solverRunTime = Int32.TryParse srt
                let! solverResult = tryParseSolverResult sr
                return SolvingStatus {transformedFileSize=transformedFileSize; solverRunMemory=solverRunMemory; solverRunTime=solverRunTime; solverResult=solverResult}
            }
    | _ -> None

let tryCollectStatistics xs =
    let rec tryCollectStatistics xs k =
        match xs with
        | [] -> k []
        | _ when List.length xs < statisticsCount -> failwithf $"""Not enough statistics records: %s{join ", " xs}"""
        | _ ->
            let stats, xs = List.splitAt statisticsCount xs
            tryCollectStatistics xs (fun ss -> k <| tryReadStatisticsFromList stats::ss)
    tryCollectStatistics xs id

let tryReadRunSolverStatus (resultFilePath : path) =
    use file = new StreamReader(resultFilePath)
    tryReadStatisticsFromList [file.ReadLine(); file.ReadLine(); file.ReadLine(); file.ReadToEnd()]

let tryReadStatistics (transformedFilePath : path, resultFilePath : path) =
    let transformationInfoFile = Path.ChangeExtension(transformedFilePath, TransformerProgram.FailInfoFileExtension)
    opt {
        match () with
        | _ when File.Exists(transformationInfoFile) ->
            let! transInfo = File.ReadAllText(transformationInfoFile) |> tryParseTransformationFail
            return TransformationStatus transInfo
        | _ when File.Exists(resultFilePath) -> return! tryReadRunSolverStatus resultFilePath
        | _ -> return! None
    }

let report dstPath srcPath (timeStatisticsFile : path) result =
    let solverRunMemory, solverRunTime = readTMPStatFile timeStatisticsFile
    let transformedFileSize = FileInfo(srcPath).Length / (1L <<< 10)
    let realResult = if solverRunTime >= MSECONDS_TIMEOUT () then SOLVER_TIMELIMIT else result
    let stat = {transformedFileSize=transformedFileSize; solverRunMemory=solverRunMemory; solverRunTime=solverRunTime; solverResult=realResult}
    writeStatistics dstPath stat
    realResult
