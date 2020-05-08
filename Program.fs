module FLispy.Program

open FLispy.Solvers


[<EntryPoint>]
let main args =
    let tip = "/home/columpio/Desktop/benchmarks/TIP", 1
    let reynolds = "/home/columpio/Desktop/benchmarks/Reynolds", 2
    let reynolds_tr = "/home/columpio/Desktop/benchmarks/Reynolds-transformed", 2
    if true then
//    if false then
//        CVC4FiniteSolver().EncodeSingleFile("/home/columpio/Desktop/benchmarks/TIP/tip2015/list_nat_elem.smt2") |> List.iter (printfn "%O")
        CVC4FiniteSolver().EncodeSingleFile("/home/columpio/Desktop/benchmarks/TIP/tip2015/list_Select.smt2") |> List.iter (printfn "%O")
//        let baseTIP = "/home/columpio/Desktop/benchmarks/TIP"
//        ResultTable.GenerateResultTable [baseTIP + ".CVC4Finite.CVC4FiniteAnswers"; baseTIP + ".Eldarica.EldaricaAnswers"; baseTIP + ".Z3.Z3Answers"]
    else
        // A /\ E x. p(x) <-> E x. (A /\ p(x))
        // !A -> E x. p(x) <-> E x. (!A -> p(x))
//        let tool = CVC4FiniteSolver()
//        let tool = EldaricaSolver()
        let overwrite = false
        let tools : ISolver list = [CVC4FiniteSolver()]
        for tool in tools do
            for dirname, to_clauses in [tip] do //; reynolds; reynolds_tr] do
                let dir = tool.GenerateClauses dirname to_clauses
                tool.RunOnBenchmarkSet overwrite dir |> ignore
    0
