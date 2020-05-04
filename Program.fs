module FLispy.Program

open System.IO
open FLispy.ParseExtension
open FLispy.Solvers
open Lexer


[<EntryPoint>]
let main args =
//    if true then
    if false then
        let file = "/home/columpio/Desktop/benchmarks/TIP/tip2015/nat_boring_max_min_abs.smt2"
        let printExprs file =
            file |> List.map toString |> join "\n" |> printfn "%s"
//        file |> parseToTerms (fun _ -> id) |> printExprs
        let tool = CVC4FiniteSolver()
        tool.SolveWithTime file |> printfn "%O"
//        file |> to_cvc4 functions_to_clauses |> List.head |> printExprs
//        file |> parseToTerms comm_to_clauses |> List.concat |> printExprs
    else
        let tip = "/home/columpio/Desktop/benchmarks/TIP", 1
        let reynolds = "/home/columpio/Desktop/benchmarks/Reynolds", 2
        let reynolds_tr = "/home/columpio/Desktop/benchmarks/Reynolds-transformed", 2
//        let tool = CVC4FiniteSolver()
//        let tool = EldaricaSolver()
        let tools : ISolver list = [CVC4FiniteSolver(); EldaricaSolver(); Z3Solver()] //; Z3Solver()]
        for tool in tools do
            for dirname, to_clauses in [tip] do //; reynolds; reynolds_tr] do
                let dir = tool.GenerateClauses dirname to_clauses
                tool.RunOnBenchmarkSet dir |> ignore
    0
