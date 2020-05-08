module FLispy.ResultTable
open System.IO
open System.Globalization
open System.Text.RegularExpressions
open CsvHelper

let private writeEmptyResult (csv : CsvWriter) =
    csv.WriteField("")
    csv.WriteField("")

let private writeSolverResult (csv : CsvWriter) time result =
    csv.WriteField(sprintf "%d" time)
    csv.WriteField(sprintf "%O" result)

let private resultRegex = Regex @"(\d+),(\w+)"

let GenerateResultTable directories =
    let filename = Path.ChangeExtension(Path.GetTempFileName(), "csv")
    use writer = new StreamWriter(filename)
    use csv = new CsvWriter(writer, CultureInfo.InvariantCulture)
    let generateResultLine testName resultFileNames =
        csv.WriteField(testName)
        for resultFileName in resultFileNames do
            if File.Exists(resultFileName) then
                let result = resultRegex.Match(File.ReadAllLines(resultFileName).[0]).Groups
                let time = int <| result.[1].Value
                let answer = result.[2].Value
                writeSolverResult csv time answer
            else writeEmptyResult csv
        csv.NextRecord()
    walk_through_simultaneously directories generateResultLine
    printfn "Table written to %s" filename
