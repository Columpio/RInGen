module FLispy.Program

open System
open System.IO
open FLispy.ParseExtension
open Lexer

let parse_file filename =
    let text = sprintf "(%s)" <| System.IO.File.ReadAllText(filename)
    try
        let (PList exprs) = parse_string text
        exprs
    with _ -> printfn "%s" filename; reraise ()

//let top_commands exprs =
//    let top_command = function
//        | List (Symbol comm::_) -> Some comm
//        | _ -> None
//    exprs |> List.choose top_command |> Set.ofList |> Set.toList

let walk_through (directory : string) postfix transform =
    let rec walk sourceFolder destFolder =
        if not <| Directory.Exists(destFolder) then
            Directory.CreateDirectory(destFolder) |> ignore
        for file in Directory.GetFiles(sourceFolder) do
            let name = Path.GetFileName(file)
            let dest = Path.Combine(destFolder, name)
            transform file dest
        for folder in Directory.GetDirectories(sourceFolder) do
            let name = Path.GetFileName(folder)
            let dest = Path.Combine(destFolder, name)
            walk folder dest
    let name' = Path.ChangeExtension(Path.GetDirectoryName(directory), postfix+".clauses")
    walk directory name'

let generate_clauses directory postfix transform =
    let mutable files = 0
    let mutable successful = 0
    let mutable total_generated = 0
    let mapFile (src : string) dst =
        if src.EndsWith(".smt2") then
//            printfn "Transforming: %s" src
            files <- files + 1
            let exprs = parse_file src
            try
                let newTests = transform exprs
                for testIndex, newTest in List.indexed newTests do
                    let lines = List.map toString newTest
                    let path = Path.ChangeExtension(dst, sprintf ".%d.smt2" testIndex)
                    File.WriteAllLines(path, lines)
                    total_generated <- total_generated + 1
                successful <- successful + 1
            with e -> printfn "Exception in %s: %O" src e.Message
    walk_through directory postfix mapFile
    printfn "All files:       %d" files
    printfn "Successful:      %d" successful
    printfn "Total generated: %d" total_generated

[<EntryPoint>]
let main args =
    if Array.length args <> 1 then
        failwith "Invalid number of arguments"
    let dirname = Array.item 0 args
//    if true then
    if false then
        let file = "/home/columpio/Desktop/benchmarks/prod/prop_47.smt2" |> parse_file
        let printExprs file =
            file |> List.map toString |> join "\n" |> printfn "%s"
        file |> parseToTerms (fun _ -> id) |> printExprs
        printfn ""
        file |> to_cvc4 |> printExprs
//        file |> parseToTerms comm_to_clauses |> List.concat |> printExprs
    else
        generate_clauses dirname ".cvc4" to_cvc4
        generate_clauses dirname "" exprsToSetOfCHCSystems
    0
