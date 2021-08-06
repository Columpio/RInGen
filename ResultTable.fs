module RInGen.ResultTable
open System.Collections.Generic
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

let private fileResult filename = rawFileResult filename |> Option.bind parseResultPair

let private substituteRelations exts filenames =
    List.map2 (fun ext filename -> Path.ChangeExtension(filename, ext)) exts filenames

let private collectAllResults (exts : string list) directories =
    let results = System.Collections.Generic.Dictionary<_, _>()
    let generateResultLine testName resultFileNames =
        let realFileNames = substituteRelations exts resultFileNames
        let line = realFileNames |> List.map fileResult
        results.Add(testName, line)
    walk_through_simultaneously directories generateResultLine
    results |> Seq.map (fun kvp -> kvp.Key, kvp.Value) |> List.ofSeq

let private BuildResultTable writeHeader writeResult writeStatistics (filename : string) header results =
    use writer = new StreamWriter(filename)
    use csv = new CsvWriter(writer, CultureInfo.InvariantCulture)
    csv.WriteField("Filename")
    for headerEntry in header do
        writeHeader csv headerEntry
    csv.NextRecord()
    writeStatistics csv results
    for testName, line in results do
        csv.WriteField(testName)
        for result in line do
            writeResult csv result
        csv.NextRecord()
    filename

let private GenerateResultTable writeHeader writeResult writeStatistics originalDirectory (names : string list) (exts : string list) directories =
    let results = collectAllResults exts directories
    let tablePath = Path.ChangeExtension(originalDirectory, ".csv")
    BuildResultTable writeHeader writeResult writeStatistics tablePath names results

module Statistics =
    type Checker (name, checker : SolverResult -> bool, checkUnique) =
        member x.Name = $"""%s{name}%s{if checkUnique then " Unique" else ""}"""
        member x.Check result line = checker result && (not checkUnique || List.countWith checker line = 1)
        new (name, checker) = Checker(name, checker, false)

    let checkers = [
        Checker("SAT", isSAT)
        Checker("SAT", isSAT, true)
        Checker("SAT: Finite Model", function SAT FiniteModel -> true | _ -> false)
        Checker("SAT: Elem Formula", function SAT ElemFormula -> true | _ -> false)
        Checker("SAT: SizeElem Formula", function SAT SizeElemFormula -> true | _ -> false)
        Checker("UNSAT", isUNSAT)
        Checker("UNSAT", isUNSAT, true)
        Checker("UNKNOWN", isUNKNOWN)
        Checker("ERROR", isERROR)
        Checker("TIMELIMIT", isTIMELIMIT)
        Checker("OUTOFMEMORY", isOUTOFMEMORY)
    ]
    let empty = List.map (fun s -> s, 0) checkers

    let add result line =
        let addOne (checker : Checker, count) =
            checker, if checker.Check result line then count + 1 else count
        List.map addOne

let private solverColumnNames solverName = $"%s{solverName}Time", $"%s{solverName}Result"
let private writeSolverColumnNames writer (t, r) = writer t; writer r
let private generateAndWriteSolverColumnNames writer solverName = solverColumnNames solverName |> writeSolverColumnNames writer
let private writeResultToString writer time answer =
    writer $"%d{time}"
    writer $"%O{answer}"
let private readResult reader (timeField, resField) = parseResultPair(reader timeField, reader resField)

module private ReadableTable =
    let writeResult (csv : CsvWriter) = function
        | Some(time, answer) -> writeResultToString csv.WriteField time answer
        | None -> csv.WriteField(""); csv.WriteField("")

    let writeStatistics (csv : CsvWriter) results =
        let collectStatistics stat line = function
            | Some(_, result) -> Statistics.add result line stat
            | None -> stat
        let results = List.map snd results
        let columns = results |> List.transpose
        let rows = results |> List.map (List.choose (function Some(_, result) -> Some result | None -> None))
        let statistics = List.map (List.fold2 collectStatistics Statistics.empty rows >> List.map snd) columns |> List.transpose
        for checker, line in List.zip Statistics.checkers statistics do
            csv.WriteField(checker.Name)
            for stat in line do
                csv.WriteField("")
                csv.WriteField($"%d{stat}")
            csv.NextRecord()

let GenerateReadableResultTable =
    let writeHeader (csv : CsvWriter) solverName =
        generateAndWriteSolverColumnNames csv.WriteField solverName
    GenerateResultTable writeHeader ReadableTable.writeResult ReadableTable.writeStatistics

let GenerateLaTeXResultTable =
    let timeToString n = $"%d{n}"
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

let private dropStatistics (csv : CsvReader) =
    List.iter (fun _ -> csv.Read() |> ignore) Statistics.checkers

let private loadTable (csv : CsvReader) =
    csv.Read() |> ignore
    csv.ReadHeader() |> ignore
    let filenameField, header = csv.Context.HeaderRecord |> List.ofArray |> List.uncons
    let headerGrouped = List.evenPairs header
    dropStatistics csv
    let table = Dictionary()
    while csv.Read() do
        let results = headerGrouped |> List.map (readResult csv.GetField)
        table.Add(csv.GetField(filenameField), results)
    headerGrouped, table

let private addNewResults (table : Dictionary<_,_>) resultsDirectory =
    let addNewResults absoluteFilename relativeFilename =
        let result = fileResult absoluteFilename
        table.[relativeFilename] <- List.addLast result table.[relativeFilename]
    walk_through resultsDirectory "" addNewResults |> ignore

let AddResultsToTable (tablePath : string) solverName resultsDirectory =
    use reader = new StreamReader(tablePath)
    use csv = new CsvReader(reader, CultureInfo.InvariantCulture)
    let header, table = loadTable csv
    addNewResults table resultsDirectory // modifies table
    let header = List.addLast (solverColumnNames solverName) header
    let table = Dictionary.toList table
    BuildResultTable (fun csv -> writeSolverColumnNames csv.WriteField) ReadableTable.writeResult ReadableTable.writeStatistics tablePath header table
