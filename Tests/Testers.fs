[<AutoOpen>]
module Tests.Testers
open SMTLIB2
open System.Text.RegularExpressions

type FileTransformationComparator () =
    inherit FileComparator ()

    let compareTransInfoFiles truthFile candidateFile =
        match File.tryFindDistinctLines truthFile candidateFile with
        | Some (l1, l2) -> Assert.Fail($"{candidateFile} content is distinct from {truthFile}:\nTruth: {l1}\n  New: {l2}")
        | None -> ()

    let compareFormulas truthFile candidateFile =
        compareTransInfoFiles truthFile candidateFile //TODO: make something more specific

    override x.CompareContents (truthFile : string) candidateFile =
        match Path.GetExtension(truthFile) with
        | ext when ext = Transformers.TransformerProgram.FailInfoFileExtension ->
            compareTransInfoFiles truthFile candidateFile
        | _ -> compareFormulas truthFile candidateFile

type FileSolverComparator () =
    inherit FileComparator ()

    override x.CompareContents truthFile candidateFile =
        let truthStatus = Statistics.tryReadRunSolverStatus truthFile
        let candidateStatus = Statistics.tryReadRunSolverStatus candidateFile
        match truthStatus, candidateStatus with
        | None, None -> ()
        | Some(Statistics.SolvingStatus truthStatus), Some(Statistics.SolvingStatus candidateStatus) ->
            Assert.AreEqual(truthStatus.solverResult, candidateStatus.solverResult,
                            $"For {candidateFile} have gold status {truthStatus.solverResult} which became {candidateStatus.solverResult}")
            let delta = 30_000.0 // 30 seconds time change possible
            Assert.AreEqual(truthStatus.solverRunTime, candidateStatus.solverRunTime, delta,
                            $"For {candidateFile} has same status but time {candidateStatus.solverRunTime} diverge from gold time {truthStatus.solverRunTime}")
        | _ -> Assert.Fail($"{candidateFile} and {truthStatus} diverge!")

type DirectoryTransformationComparator () =
    inherit DirectoryComparator(FileTransformationComparator ())

type DirectorySolverComparator () =
    inherit DirectoryComparator(FileSolverComparator ())

[<AbstractClass>]
type Tester<'filenameEntry> (c : IComparator) =
    abstract member FullPath : 'filenameEntry -> 'filenameEntry
    abstract member OutputPath : 'filenameEntry -> path
    abstract member GoldPath : 'filenameEntry -> path
    abstract member RealGeneratedPath : path -> path

    member x.Compare = c.Compare

    member x.Test (fe : 'filenameEntry) config =
        let path = x.FullPath fe
        let outPath = x.OutputPath path
        if Directory.Exists(outPath) then Directory.Delete(outPath, true)
        let runCommand = config path outPath
        print_extra_verbose $"TEST run with: ringen {runCommand}"
        Assert.Zero(ConsoleRunner.main(Regex("\s+").Split(runCommand)), "Congiguration run halted with an error")
        let targetPath = x.RealGeneratedPath outPath
        let gold = x.GoldPath path
        c.Compare gold targetPath

type FileTester (fc : FileComparator, fileFolder) =
    inherit Tester<path * string>(fc)

    let ringenFolder = __SOURCE_DIRECTORY__
    let testsFolder = Path.Join(ringenFolder, fileFolder)

    override x.FullPath fe =
        let name, postfix = fe
        Path.Join(testsFolder, name), postfix
    override x.OutputPath fe =
        let path, postfix = fe
        Path.ChangeExtension(path, postfix + ".generated")
    override x.GoldPath  fe =
        let path, postfix = fe
        Path.ChangeExtension(path, postfix + ".gold.smt2")
    override x.RealGeneratedPath path = Directory.GetFiles(path).[0]

    member x.RunTest name postfix config =
        x.Test (name, postfix) (fun (path, _) -> config path)

    member x.RunSolver name postfix timelimit (solver : Program) =
        let (origPath, _) as path = x.FullPath(name, postfix)
        let outPath = x.OutputPath path
        Options.SECONDS_TIMEOUT <- timelimit
        match solver.Run origPath (Some outPath) with
        | None -> Assert.Fail("Configuration run halted with an error")
        | Some targetPath ->
        let gold = x.GoldPath path
        x.Compare gold targetPath

    member private x.RunTTAPortfolioWithConfigs name postfix timelimit tip configs =
        let config = {tip=tip; sync_terms=false; child_transformer=None}
        let ps = PortfolioSolver(configs config)
        x.RunSolver name postfix timelimit ps

    member private x.RunTTAAloneCVCWithTip name postfix timelimit tip =
        x.RunTTAAloneWith name postfix timelimit tip (CVCFiniteSolver() :> SolverProgramRunner)

    member x.RunTTAAloneCVC name postfix timelimit = x.RunTTAAloneCVCWithTip name postfix timelimit false
    member x.RunTTAAloneCVCTIP name postfix timelimit = x.RunTTAAloneCVCWithTip name postfix timelimit true

    member private x.RunTTAAloneVampireWithTip name postfix timelimit tip =
        x.RunTTAAloneWith name postfix timelimit tip (VampireSolver() :> SolverProgramRunner)

    member x.RunTTAAloneVampire name postfix timelimit = x.RunTTAAloneVampireWithTip name postfix timelimit false
    member x.RunTTAAloneVampireTIP name postfix timelimit = x.RunTTAAloneVampireWithTip name postfix timelimit true

    member private x.RunTTAAloneWith name postfix timelimit tip solver =
        let transformations config = [
            TTATransformerProgram(config) :> TransformerProgram, solver
        ]
        x.RunTTAPortfolioWithConfigs name postfix timelimit tip transformations

    member private x.RunTTAPortfolioWithTip name postfix timelimit tip =
        let transformations config = [
            FreeSortsTransformerProgram(config) :> TransformerProgram, CVCFiniteSolver() :> SolverProgramRunner
            TTATransformerProgram(config), CVCFiniteSolver()
        ]
        x.RunTTAPortfolioWithConfigs name postfix timelimit tip transformations

    member x.RunTTAPortfolio name postfix timelimit = x.RunTTAPortfolioWithTip name postfix timelimit false

type DirectoryTester (c : DirectoryComparator, directoryFolder) =
    inherit Tester<path * string>(c)

    let testsProject = __SOURCE_DIRECTORY__
    let testsFolder = Path.Join(testsProject, "tests")
    let generatedBasePath = Path.Join(testsFolder, "generated")
    let goldBasePath = Path.Join(testsFolder, "gold")
    let origFolder = Path.Join(testsFolder, directoryFolder)

    override x.FullPath fe =
        let _, name = fe
        origFolder, name
    override x.OutputPath fe =
        let _, name = fe
        $"{Path.Join(generatedBasePath, name).TrimEnd(Path.DirectorySeparatorChar)}{Path.DirectorySeparatorChar}"
    override x.GoldPath fe =
        let _, name = fe
        Path.Join(goldBasePath, name) |> x.RealGeneratedPath
    override x.RealGeneratedPath outputPath =
        Directory.GetDirectories outputPath |> Array.maxBy String.length

    member x.RunTest postfix config =
        x.Test ("", postfix) (fun (path, _) -> config path)

type FileTransformationTester (fileFolder) =
    inherit FileTester(FileTransformationComparator(), fileFolder)

type FileSolverTester (fileFolder) =
    inherit FileTester(FileSolverComparator(), fileFolder)

type DirectoryTransformationTester (directoryFolder) =
    inherit DirectoryTester(DirectoryTransformationComparator(), directoryFolder)

type DirectorySolverTester (directoryFolder) =
    inherit DirectoryTester(DirectorySolverComparator(), directoryFolder)
