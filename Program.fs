module FLispy.Program

open System
open System.IO
open FLispy.ParseExtension
open FLispy.Solvers
open Lexer

let rec hasInt = function
    | PList es -> List.exists hasInt es
    | PNumber _ -> true
    | PComment -> false
    | PMatch(t, ts) -> hasInt t || List.exists (fun (a, b) -> hasInt a || hasInt b) ts
    | PSymbol "Int" -> true
    | PSymbol _ -> false

let parse_file filename =
    let text = sprintf "(%s)" <| System.IO.File.ReadAllText(filename)
    try
        let (PList exprs) = parse_string text
        exprs |> List.filter ((<>) PComment)
    with _ -> printfn "%s" filename; reraise ()

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
    let name' = directory + postfix
    walk directory name'
    name'

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
                if not <| List.exists hasInt exprs then
                    let newTests = transform exprs
                    for testIndex, newTest in List.indexed newTests do
                        let lines = List.map toString newTest
                        let path = Path.ChangeExtension(dst, sprintf ".%d.smt2" testIndex)
                        File.WriteAllLines(path, lines)
                        total_generated <- total_generated + 1
                successful <- successful + 1
            with e -> printfn "Exception in %s: %O" src e.Message
    let output_directory = walk_through directory postfix mapFile
    printfn "All files:       %d" files
    printfn "Successful:      %d" successful
    printfn "Total generated: %d" total_generated
    output_directory

let run_solver (solver : ISolver) dir result_postfix =
    let run_file src dst =
        try
            printfn "Running solver on %s" src
            let answer, time = solver.SolveWithTime(src)
            File.WriteAllText(dst, sprintf "%d,%O" time answer)
        with e -> printfn "Exception in %s: %s" src dst
    walk_through dir result_postfix run_file

[<EntryPoint>]
let main args =
    if Array.length args <> 1 then
        failwith "Invalid number of arguments"
    let dirname = Array.item 0 args
//    if true then
    if false then
        let file = "/home/columpio/Desktop/benchmarks/TIP/tip2015/nat_boring_max_min_abs.smt2" |> parse_file
        let printExprs file =
            file |> List.map toString |> join "\n" |> printfn "%s"
//        file |> parseToTerms (fun _ -> id) |> printExprs
//        printfn ""
        file |> to_cvc4 functions_to_clauses |> List.head |> printExprs
//        file |> parseToTerms comm_to_clauses |> List.concat |> printExprs
    else
        let tip = "/home/columpio/Desktop/benchmarks/TIP", functions_to_clauses
        let reynolds = "/home/columpio/Desktop/benchmarks/Reynolds", clauses_to_clauses
        let reynolds_tr = "/home/columpio/Desktop/benchmarks/Reynolds-transformed", clauses_to_clauses
        let cvc4 = CVC4FiniteSolver()
        for dirname, to_clauses in [tip; reynolds; reynolds_tr] do
            let cvc_dir = generate_clauses dirname ".cvc4" (to_cvc4 to_clauses)
            run_solver cvc4 cvc_dir ".cvc4answers" |> ignore
        ()
//        walk_through cvc_dir ".cvc4answers" (fun src _ -> cvc4.SolveWithTime(src) |> printfn "%s %O" src) |> ignore
//        generate_clauses dirname ".clauses" exprsToSetOfCHCSystems |> ignore
    0
