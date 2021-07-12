module RInGen.ResultTable
open System.IO
open System.Globalization
open System.Text.RegularExpressions
open CsvHelper
open SolverResult

let private resultRegex = Regex @"(\d+),([\w ]+\w)"

let rawFileResult filename =
    if not <| File.Exists(filename) then None else
    let result = resultRegex.Match(File.ReadAllLines(filename).[0]).Groups
    let time = result.[1].Value
    let answer = result.[2].Value
    Some (time, answer)

let private substituteRelations exts filenames =
    List.map2 (fun ext filename -> Path.ChangeExtension(filename, ext)) exts filenames

let private collectAllResults (exts : string list) directories =
    let results = System.Collections.Generic.Dictionary<_, _>()
    let generateResultLine testName resultFileNames =
        let realFileNames = substituteRelations exts resultFileNames
        let line = realFileNames |> List.map (fun resultFileName -> rawFileResult resultFileName |> Option.map parseResultPair)
        results.Add(testName, line)
    walk_through_simultaneously directories generateResultLine
    results |> Seq.map (fun kvp -> kvp.Key, kvp.Value) |> List.ofSeq

let private GenerateResultTable writeHeader writeResult writeStatistics (names : string list) (exts : string list) directories =
    let filename = Path.ChangeExtension(Path.GetTempFileName(), "csv")
    use writer = new StreamWriter(filename)
    use csv = new CsvWriter(writer, CultureInfo.InvariantCulture)
    csv.WriteField("Filename")
    for solverName in names do
        writeHeader csv solverName
    csv.NextRecord()
    let results = collectAllResults exts directories
    writeStatistics csv results
    for testName, line in results do
        csv.WriteField(testName)
        for result in line do
            writeResult csv result
        csv.NextRecord()
    filename

let GenerateReadableResultTable =
    let writeResult (csv : CsvWriter) = function
        | Some(time, answer) ->
            csv.WriteField($"%d{time}")
            csv.WriteField($"%O{answer}")
        | None -> csv.WriteField(""); csv.WriteField("")

    let writeHeader (csv : CsvWriter) solverName =
        csv.WriteField$"%s{solverName}Time"
        csv.WriteField$"%s{solverName}Result"

    let writeStatistics (csv : CsvWriter) results =
        let names = ["SAT"; "UNSAT"; "UNKNOWN"; "ERROR"; "TIMELIMIT"; "OUTOFMEMORY"]
        let empty_stat = names |> List.map (fun s -> s, 0) |> Map.ofList
        let collectStatistics stat = function
            | Some(_, result) ->
                let name = onlyStatus result
                let count = Map.find name stat
                Map.add name (1 + count) stat
            | None -> stat
        let columns = results |> List.map snd |> List.transpose
        let statistics = List.map (List.fold collectStatistics empty_stat) columns
        for name in names do
            csv.WriteField(name)
            for stat in statistics do
                csv.WriteField("")
                csv.WriteField($"%d{Map.find name stat}")
            csv.NextRecord()

    GenerateResultTable writeHeader writeResult writeStatistics

let GenerateLaTeXResultTable =
    let timeToString n = n |> sprintf "%d"
    let TIMEOUT = timeToString <| 2 * (MSECONDS_TIMEOUT ())
    let writeEmptyResult (csv : CsvWriter) =
        csv.WriteField(TIMEOUT)

    let writeResult (csv : CsvWriter) = function
        | Some (time, answer) ->
            match answer with
            | SAT _
            | UNSAT
            | TIMELIMIT -> csv.WriteField(timeToString time)
            | _ -> writeEmptyResult csv
        | None -> writeEmptyResult csv

    let writeHeader (csv : CsvWriter) solverName =
        csv.WriteField(solverName)

    GenerateResultTable writeHeader writeResult (fun _ _ -> ())

let PrintReadableResultTable names directories =
    let timeWidth, resultWidth, nameWidth =
        let mutable timeWidth = 1
        let mutable resultWidth = 1
        let mutable nameWidth = 1
        let calcWidths (testName : string) resultFileNames =
            nameWidth <- max nameWidth testName.Length
            for resultFileName in resultFileNames do
                match rawFileResult resultFileName with
                | Some (time, answer) ->
                    timeWidth <- max timeWidth time.Length
                    resultWidth <- max resultWidth answer.Length
                | None -> ()
        walk_through_simultaneously directories calcWidths
        timeWidth, resultWidth, nameWidth
    let printResultLine (testName : string) resultFileNames =
        printf "%s " <| testName.PadRight(nameWidth)
        for resultFileName in resultFileNames do
            let time, answer = Option.defaultValue ("", "") (rawFileResult resultFileName)
            let time = time.PadRight(timeWidth)
            let answer = answer.PadRight(resultWidth)
            printf $"%s{time} %s{answer} "
        printfn ""
    printf "%s " ("Name".PadRight(nameWidth))
    names |> List.map (fun (name : string) -> name.PadRight(timeWidth + resultWidth + 2)) |> join "" |> printfn "%s"
    walk_through_simultaneously directories printResultLine
