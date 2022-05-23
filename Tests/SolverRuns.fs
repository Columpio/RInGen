module Tests.SolverRuns
open NUnit.Framework
open RInGen
open RInGen.Transformers
open RInGen.Solvers

[<TestFixture>]
type TIPSolverTests () =
    inherit DirectorySolverTester("TIP")

    [<Test>]
    member x.OriginalSolveVampire1Sec () =
        let name = "OriginalSolve"
        let config origPath outPath = $"-o {outPath} --timelimit 1 solve --solver vampire --path {origPath} -t --tip"
        x.RunTest name config

    [<Test>]
    member x.OriginalSolveVampire100Sec () =
        let name = "OriginalSolveVampire100Sec"
        let config origPath outPath = $"-o {outPath} --timelimit 100 solve --solver vampire --path {origPath} -t --tip"
        x.RunTest name config

[<TestFixture>]
type SampleSolverTests () =
    inherit FileSolverTester("samples")

    [<Test>]
    member x.Productive_use_of_failure_app_inj1_OnVampire60sec () =
        // finishes in 32 seconds with SAT
        // winning configuration is dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3
        let config origPath outPath = $"-o {outPath} --timelimit 600 solve --solver vampire --path {origPath} -t --tip"
        x.RunTest "productive_use_of_failure_app_inj1.smt2" "" config

    [<Test>]
    member x.prop_01_OnVampire1sec () =
        let config origPath outPath = $"-o {outPath} --timelimit 1 solve --solver vampire --path {origPath}"
        x.RunTest "prop_01.smt2" ".asis" config

    [<Test>]
    member x.prop_32_trans_OnVampire1sec () =
        let config origPath outPath = $"-o {outPath} --timelimit 1 solve --solver vampire --path {origPath} -t"
        x.RunTest "prop_32.smt2" ".trans" config

    [<Test>]
    member x.fast_unsat_trans_OnVampire10sec () =
        let config origPath outPath = $"-o {outPath} --timelimit 10 solve --solver vampire --path {origPath} -t"
        x.RunTest "fast_unsat.smt2" ".trans" config

    [<Test>]
    member x.even_OnCVC1sec () =
        let config origPath outPath = $"-o {outPath} --timelimit 1 solve --solver cvc_fmf --path {origPath} -t"
        x.RunTest "even.smt2" "" config

    [<Test>]
    member x.test_OnCVC1sec () =
        let config origPath outPath = $"-o {outPath} --timelimit 1 solve --solver cvc_fmf --path {origPath} -t"
        x.RunTest "test.smt2" ".models" config

    [<Test>]
    member x.evenTtaTest () =
        let config origPath outPath = $"-o {outPath} --timelimit 30 solve --solver cvc_fmf --path {origPath} -t --tta-transform"
        x.RunTest "even.smt2" ".tta" config

    [<Test>]
    member x.evenSatTtaVampireTest () =
        let config origPath outPath = $"-o {outPath} --timelimit 10 solve --solver vampire --path {origPath} -t --tta-transform"
        x.RunTest "even.smt2" ".tta_sat" config

    [<Test>]
    member x.evenUnsatTtaVampireTest () =
        let config origPath outPath = $"-o {outPath} --timelimit 10 solve --solver vampire --path {origPath} -t --tta-transform"
        x.RunTest "even.unsat.smt2" ".tta_unsat" config

    [<Test>]
    member x.mod_same () =
        let config origPath outPath = $"-o {outPath} --timelimit 10 solve --solver cvc_fmf --path {origPath} -t --tip --tta-transform"
        x.RunTest "mod_same.smt2" ".tta_unsat" config

    [<Test>]
    member x.tta_ltlt () =
        let config origPath outPath = $"-o {outPath} --timelimit 10 solve --solver cvc_fmf --path {origPath} -t --tta-transform"
        x.RunTest "ltlt.smt2" ".tta" config

    [<Test>]
    member x.fmf_with_tta_ltlt () =
        let config = {tip=false; sync_terms=false; child_transformer=None}
        let transformations = [
            FreeSortsTransformerProgram(config) :> TransformerProgram, CVCFiniteSolver() :> SolverProgramRunner
            TTATransformerProgram(config), CVCFiniteSolver()
        ]
        let ps = PortfolioSolver(transformations)
        x.RunSolver "ltlt.smt2" ".fmf_with_tta" 3 ps

    [<Test>]
    member x.tta_ltlt_unsat () =
        let config origPath outPath = $"-o {outPath} --timelimit 10 solve --solver cvc_fmf --path {origPath} -t --no-isolation --tta-transform"
        x.RunTest "ltlt_unsat.smt2" ".tta_unsat" config
        
    [<Test>]
    member x.tta_mccarthy () =
        let config origPath outPath = $"-o {outPath} --timelimit 600 solve --solver cvc_fmf --path {origPath} -t --tip --no-isolation --tta-transform"
        x.RunTest "mccarthy91_M2.smt2" ".tta" config

    [<Test>]
    member x.tta_prop20 () =
        let config origPath outPath = $"-o {outPath} --timelimit 10 solve --solver cvc_fmf --path {origPath} -t --tip --no-isolation --tta-transform"
        x.RunTest "prop_20.smt2" ".tta" config
