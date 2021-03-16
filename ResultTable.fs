module RInGen.ResultTable
open System.IO
open System.Globalization
open System.Text.RegularExpressions
open CsvHelper
open SolverResult

let private resultRegex = Regex @"(\d+),(\w+)"

let private substituteRelations exts filenames =
    List.map2 (fun ext filename -> Path.ChangeExtension(filename, ext)) exts filenames

let private GenerateResultTable writeHeader writeSolverResult writeEmptyResult (names : string list) (exts : string list) directories =
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
            if File.Exists(resultFileName) then
                let result = resultRegex.Match(File.ReadAllLines(resultFileName).[0]).Groups
                let time = int <| result.[1].Value
                let answer = result.[2].Value
                writeSolverResult csv time answer
            else writeEmptyResult csv
        csv.NextRecord()
    walk_through_simultaneously directories generateResultLine
    filename

let GenerateReadableResultTable =
    let writeEmptyResult (csv : CsvWriter) =
        csv.WriteField("")
        csv.WriteField("")

    let writeSolverResult (csv : CsvWriter) time result =
        csv.WriteField(sprintf "%d" time)
        csv.WriteField(sprintf "%s" result)

    let writeHeader (csv : CsvWriter) solverName =
        csv.WriteField(sprintf "%sTime" solverName)
        csv.WriteField(sprintf "%sResult" solverName)

    GenerateResultTable writeHeader writeSolverResult writeEmptyResult

let GenerateLaTeXResultTable =
    let timeToString n = n |> sprintf "%d"
    let writeEmptyResult (csv : CsvWriter) =
        csv.WriteField(timeToString <| 2 * (MSECONDS_TIMEOUT ()))

    let writeSolverResult (csv : CsvWriter) time result =
        match parseSolverResult result with
        | SAT
        | UNSAT
        | TIMELIMIT -> csv.WriteField(timeToString time)
        | _ -> writeEmptyResult csv

    let writeHeader (csv : CsvWriter) solverName =
        csv.WriteField(solverName)

    GenerateResultTable writeHeader writeSolverResult writeEmptyResult

let PrintReadableResultTable names directories =
    let timeWidth, resultWidth, nameWidth =
        let mutable timeWidth = 1
        let mutable resultWidth = 1
        let mutable nameWidth = 1
        let calcWidths (testName : string) resultFileNames =
            nameWidth <- max nameWidth testName.Length
            for resultFileName in resultFileNames do
                if File.Exists(resultFileName) then
                    let result = resultRegex.Match(File.ReadAllLines(resultFileName).[0]).Groups
                    let time = result.[1].Value.Length
                    let answer = result.[2].Value.Length
                    timeWidth <- max timeWidth time
                    resultWidth <- max resultWidth answer
        walk_through_simultaneously directories calcWidths
        timeWidth, resultWidth, nameWidth
    let printResultLine (testName : string) resultFileNames =
        printf "%s " <| testName.PadRight(nameWidth)
        for resultFileName in resultFileNames do
            let time, answer =
                if File.Exists(resultFileName) then
                    let result = resultRegex.Match(File.ReadAllLines(resultFileName).[0]).Groups
                    let time = result.[1].Value
                    let answer = result.[2].Value
                    time, answer
                else "", ""
            let time = time.PadRight(timeWidth)
            let answer = answer.PadRight(resultWidth)
            printf "%s %s " time answer
        printfn ""
    printf "%s " ("Name".PadRight(nameWidth))
    names |> List.map (fun (name : string) -> name.PadRight(timeWidth + resultWidth + 2)) |> join "" |> printfn "%s"
    walk_through_simultaneously directories printResultLine
