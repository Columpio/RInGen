module RInGen.ResultTable
open System.IO
open System.Globalization
open System.Text.RegularExpressions
open CsvHelper
open SolverResult

let private resultRegex = Regex @"(\d+),(\w+)"

let rawFileResult filename =
    if not <| File.Exists(filename) then None else
    let result = resultRegex.Match(File.ReadAllLines(filename).[0]).Groups
    let time = result.[1].Value
    let answer = result.[2].Value
    Some (time, answer)

let private substituteRelations exts filenames =
    List.map2 (fun ext filename -> Path.ChangeExtension(filename, ext)) exts filenames

let private GenerateResultTable writeHeader writeResult (names : string list) (exts : string list) directories =
    let filename = Path.ChangeExtension(Path.GetTempFileName(), "csv")
    use writer = new StreamWriter(filename)
    use csv = new CsvWriter(writer, CultureInfo.InvariantCulture)
    csv.WriteField("Filename")
    for solverName in names do
        writeHeader csv solverName
    csv.NextRecord()
    let generateResultLine testName resultFileNames =
        csv.WriteField(testName)
        let realFileNames = substituteRelations exts resultFileNames
        for resultFileName in realFileNames do
            writeResult csv <| rawFileResult resultFileName
        csv.NextRecord()
    walk_through_simultaneously directories generateResultLine
    filename

let GenerateReadableResultTable =
    let writeResult (csv : CsvWriter) result =
        let time, answer = Option.defaultValue ("", "") result
        csv.WriteField($"%s{time}")
        csv.WriteField($"%s{answer}")

    let writeHeader (csv : CsvWriter) solverName =
        csv.WriteField$"%s{solverName}Time"
        csv.WriteField$"%s{solverName}Result"

    GenerateResultTable writeHeader writeResult

let GenerateLaTeXResultTable =
    let timeToString n = n |> sprintf "%d"
    let TIMEOUT = timeToString <| 2 * (MSECONDS_TIMEOUT ())
    let writeEmptyResult (csv : CsvWriter) =
        csv.WriteField(TIMEOUT)

    let writeResult (csv : CsvWriter) = parseResultPair >> function
        | Some (time, answer) ->
            match answer with
            | SAT
            | UNSAT
            | TIMELIMIT -> csv.WriteField(timeToString time)
            | _ -> writeEmptyResult csv
        | None -> writeEmptyResult csv

    let writeHeader (csv : CsvWriter) solverName =
        csv.WriteField(solverName)

    GenerateResultTable writeHeader writeResult

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
