module RInGen.ResultTable
open System.Collections.Generic
open System.IO
open System.Globalization
open CsvHelper
open SolverResult

let private substituteRelations exts filenames =
    let change f (f1, f2) = f f1, f f2
    List.map2 (fun ext -> change <| fun filename -> Path.ChangeExtension(filename, ext)) exts filenames

let private collectAllResults (exts : string list) originalDirectory transAndResultDirs=
    let results = Dictionary<_, _>()
    let generateResultLine (testName : path) transAndResultFileNames =
        if Path.GetExtension(testName) <> ".smt2" then () else
        let transFileNames, resultFileNames = List.unzip transAndResultDirs
        let transAndResultFileNames = substituteRelations exts transAndResultFileNames
        let line = transAndResultFileNames |> List.map Statistics.tryReadStatistics
        results.Add(testName, line)
    walk_through_simultaneously originalDirectory transAndResultDirs generateResultLine
    results |> Dictionary.toList

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

let private GenerateResultTable writeHeader writeResult writeStatistics originalDirectory (names : string list) (exts : string list) transAndResultDirs =
    let results = collectAllResults exts originalDirectory transAndResultDirs
    let tablePath = Path.ChangeExtension(originalDirectory, ".csv")
    BuildResultTable writeHeader writeResult writeStatistics tablePath names results

module Checkers =
    type Checker (name, checker : Statistics.status -> bool, checkUnique) =
        member x.Name = $"""%s{name}%s{if checkUnique then " Unique" else ""}"""
        member x.Check result line = checker result && (not checkUnique || List.countWith checker line = 1)
        new (name, checker) = Checker(name, checker, false)

    let ifSolvingResult f = function Statistics.SolvingStatus stat -> f stat.solverResult | _ -> false

    let isSAT = function SAT _ -> true | _ -> false
    let isSAT_FM = function SAT FiniteModel -> true | _ -> false
    let isSAT_Elem = function SAT ElemFormula -> true | _ -> false
    let isSAT_SizeElem = function SAT SizeElemFormula -> true | _ -> false
    let isUNSAT = function UNSAT -> true | _ -> false
    let isERROR = function ERROR _ -> true | _ -> false
    let isUNKNOWN = function UNKNOWN _ -> true | _ -> false
    let isTIMELIMIT = function SOLVER_TIMELIMIT -> true | _ -> false
    let isOUTOFMEMORY = function OUTOFMEMORY -> true | _ -> false

    let isTIMELIMIT_TRANS = (=) <| Statistics.TransformationStatus Transformers.TRANS_TIMELIMIT
    let isOTHER_TRANS = function Statistics.TransformationStatus s -> s <> Transformers.TRANS_TIMELIMIT | _ -> false

    let checkers = [
        Checker("SAT", ifSolvingResult isSAT)
        Checker("SAT", ifSolvingResult isSAT, true)
        Checker("SAT: Finite Model", ifSolvingResult isSAT_FM)
        Checker("SAT: Elem Formula", ifSolvingResult isSAT_Elem)
        Checker("SAT: SizeElem Formula", ifSolvingResult isSAT_SizeElem)
        Checker("UNSAT", ifSolvingResult isUNSAT)
        Checker("UNSAT", ifSolvingResult isUNSAT, true)
        Checker("SKIPPED BY TRANSFORMING", isOTHER_TRANS)
        Checker("TIMELIMIT IN TRANSFORMING", isTIMELIMIT_TRANS)
        Checker("UNKNOWN", ifSolvingResult isUNKNOWN)
        Checker("ERROR", ifSolvingResult isERROR)
        Checker("TIMELIMIT IN SOLVING", ifSolvingResult isTIMELIMIT)
        Checker("OUTOFMEMORY", ifSolvingResult isOUTOFMEMORY)
    ]
    let empty = List.map (fun s -> s, 0) checkers

    let add result line =
        let addOne (checker : Checker, count) =
            checker, if checker.Check result line then count + 1 else count
        List.map addOne

let private solverColumnNames solverName =
    List.map (fun fieldName -> $"%s{solverName}{fieldName}") Statistics.fieldNames
let private writeSolverColumnNames writer columnNames = List.iter writer columnNames
let private generateAndWriteSolverColumnNames writer solverName = solverColumnNames solverName |> writeSolverColumnNames writer

module private ReadableTable =
    let writeResult (csv : CsvWriter) statOpt =
        statOpt |> Option.map (Statistics.mapResult compactStatus)
        |> Statistics.iterTry csv.WriteField

    let writeCheckers (csv : CsvWriter) results =
        let collectCheckers chk line = function
            | Some stat -> Checkers.add stat line chk
            | None -> chk
        let results = List.map snd results
        let columns = results |> List.transpose
        let rows = results |> List.map (List.choose id)
        let statistics = List.map (List.fold2 collectCheckers Checkers.empty rows >> List.map snd) columns |> List.transpose
        for checker, line in List.zip Checkers.checkers statistics do
            csv.WriteField(checker.Name)
            for stat in line do
                Statistics.iterExceptLast (fun () -> csv.WriteField($"%d{stat}")) (fun () -> csv.WriteField(""))
            csv.NextRecord()

let GenerateReadableResultTable =
    let writeHeader (csv : CsvWriter) solverName =
        generateAndWriteSolverColumnNames csv.WriteField solverName
    GenerateResultTable writeHeader ReadableTable.writeResult ReadableTable.writeCheckers

//let GenerateLaTeXResultTable =
//    let timeToString n = $"%d{n}"
//    let TIMEOUT = timeToString <| 2 * (MSECONDS_TIMEOUT ())
//    let writeEmptyResult (csv : CsvWriter) =
//        csv.WriteField(TIMEOUT)
//
//    let writeResult (csv : CsvWriter) = function
//        | Some (time, answer) ->
//            match answer with
//            | SAT _
//            | UNSAT
//            | TIMELIMIT -> csv.WriteField(timeToString time)
//            | _ -> writeEmptyResult csv
//        | None -> writeEmptyResult csv
//
//    let writeHeader (csv : CsvWriter) solverName =
//        csv.WriteField(solverName)
//
//    GenerateResultTable writeHeader writeResult (fun _ _ -> ())

//let PrintReadableResultTable names directories =
//    let timeWidth, resultWidth, nameWidth =
//        let mutable timeWidth = 1
//        let mutable resultWidth = 1
//        let mutable nameWidth = 1
//        let calcWidths (testName : string) resultFileNames =
//            nameWidth <- max nameWidth testName.Length
//            for resultFileName in resultFileNames do
//                match rawFileResult resultFileName with
//                | Some (time, answer) ->
//                    timeWidth <- max timeWidth time.Length
//                    resultWidth <- max resultWidth answer.Length
//                | None -> ()
//        walk_through_simultaneously directories calcWidths
//        timeWidth, resultWidth, nameWidth
//    let printResultLine (testName : string) resultFileNames =
//        printf "%s " <| testName.PadRight(nameWidth)
//        for resultFileName in resultFileNames do
//            let time, answer = Option.defaultValue ("", "") (rawFileResult resultFileName)
//            let time = time.PadRight(timeWidth)
//            let answer = answer.PadRight(resultWidth)
//            printf $"%s{time} %s{answer} "
//        printfn ""
//    printf "%s " ("Name".PadRight(nameWidth))
//    names |> List.map (fun (name : string) -> name.PadRight(timeWidth + resultWidth + 2)) |> join "" |> printfn "%s"
//    walk_through_simultaneously directories printResultLine

let private dropStatistics (csv : CsvReader) =
    List.iter (fun _ -> csv.Read() |> ignore) Checkers.checkers

let private loadTable (csv : CsvReader) =
    csv.Read() |> ignore
    csv.ReadHeader() |> ignore
    let filenameField, header = csv.Context.HeaderRecord |> List.ofArray |> List.uncons
    dropStatistics csv
    let table = Dictionary()
    while csv.Read() do
        let results = header |> List.map csv.GetField
        let stats = Statistics.tryCollectStatistics results
        table.Add(csv.GetField(filenameField), stats)
    header, table

let private addNewResults (table : Dictionary<_,_>) transDirectory resultsDirectory =
    let addNewResults relativeFilename =
        let transFileName = Path.Combine(transDirectory, relativeFilename)
        let resultFileName = Path.Combine(resultsDirectory, relativeFilename)
        let result = Statistics.tryReadStatistics(transFileName, resultFileName)
        table.[relativeFilename] <- List.addLast result table.[relativeFilename]
    walk_through_relative resultsDirectory addNewResults

let AddResultsToTable (tablePath : string) solverName transDirectory resultsDirectory =
    use reader = new StreamReader(tablePath)
    use csv = new CsvReader(reader, CultureInfo.InvariantCulture)
    let header, table = loadTable csv
    addNewResults table transDirectory resultsDirectory // modifies table
    let header = header @ solverColumnNames solverName
    let table = Dictionary.toList table
    BuildResultTable (fun csv -> csv.WriteField) ReadableTable.writeResult ReadableTable.writeCheckers tablePath header table
