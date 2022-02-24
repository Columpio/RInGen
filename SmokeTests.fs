module RInGen.SmokeTests
open NUnit.Framework
open System.IO
open System.Text.RegularExpressions
open RInGen

let compareTransInfoFiles truthFile candidateFile =
    match File.tryFindDistinctLines truthFile candidateFile with
    | Some (l1, l2) -> Assert.Fail($"{candidateFile} content is distinct from {truthFile}:\nTruth: {l1}\n  New: {l2}")
    | None -> ()
let compareFormulas truthFile candidateFile =
    compareTransInfoFiles truthFile candidateFile //TODO: make something more specific
let compareFileContents (truthFile : string) candidateFile =
    match Path.GetExtension(truthFile) with
    | ext when ext = Transformers.TransformerProgram.FailInfoFileExtension ->
        compareTransInfoFiles truthFile candidateFile
    | _ -> compareFormulas truthFile candidateFile
let compareFiles truthFile candidateFile =
    if not <| File.Exists(candidateFile) then Assert.Fail($"{candidateFile} does not exist so cannot compare it with {truthFile}")
    elif not <| File.Exists(truthFile) then Assert.Fail($"{truthFile} does not exist so cannot compare it with {candidateFile}")
    else compareFileContents truthFile candidateFile
let compareBenches truthPath candidatePath =
    walk_through_copy truthPath candidatePath compareFiles

[<TestFixture>]
type SamplesTests () =
    let testsProject = __SOURCE_DIRECTORY__
    let testsFolder = Path.Join(testsProject, "samples")

    let fullPath name = Path.Join(testsFolder, name)
    let outputPath path postfix = Path.ChangeExtension(path, postfix + ".generated.smt2")
    let goldPath path postfix = Path.ChangeExtension(path, postfix + ".gold.smt2")

    let testOnFileWithConfig filename postfix config =
        let path = fullPath filename
        let outPath = outputPath path postfix
        Assert.Zero(ConsoleRunner.main(Regex("\s+").Split(config path outPath)), "Transformation run halted with an error")
        let gold = goldPath path postfix
        compareFiles gold outPath

    [<Test>]
    member x.LtLtOrigTest () =
        let config path outPath = $"-o {outPath} transform --mode original {path} -t --no-isolation"
        testOnFileWithConfig "ltlt.smt2" ".orig" config

    [<Test>]
    member x.LtLtTTATest () =
        let config path outPath = $"-o {outPath} transform --mode freesorts {path} -t --no-isolation --tta-transform"
        testOnFileWithConfig "ltlt.smt2" ".tta" config
