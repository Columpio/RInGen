module Tests.Transformations
open NUnit.Framework

[<TestFixture>]
type SamplesTests () =
    inherit FileTransformationTester("samples")

    [<Test>]
    member x.LtLtOrigTest () =
        let config path outPath = $"-o {outPath} transform --mode original {path} -t --no-isolation"
        x.RunTest "ltlt.smt2" ".orig" config

    [<Test>]
    member x.LemmaOrigTest () =
        let config path outPath = $"-o {outPath} transform --mode original {path} -t --no-isolation"
        x.RunTest "lemmas_with_new_syntax.smt2" "" config

    [<Test>]
    member x.LtLtTTATest () =
        let config path outPath = $"-o {outPath} transform --mode freesorts {path} -t --no-isolation --tta-transform"
        x.RunTest "ltlt.smt2" ".tta" config

[<TestFixture>]
type TIPTests () =
    inherit DirectoryTransformationTester("TIP")

    [<Test>]
    member x.OriginalTrans () =
        let name = "OriginalTrans"
        let config origPath outPath = $"-o {outPath} transform --mode original {origPath} -t --tip --no-isolation"
        x.RunTest name config
