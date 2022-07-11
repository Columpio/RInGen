[<AutoOpen>]
module Tests.Testers
open System
open NUnit.Framework
open System.IO
open System.Text.RegularExpressions
open RInGen
open RInGen.Solvers

type IComparator =
    abstract member Compare : path -> path -> unit

[<AbstractClass>]
type FileComparator () =
    abstract member CompareContents : path -> path -> unit

    interface IComparator with
        member x.Compare truthFile candidateFile =
            if not <| File.Exists(candidateFile) then Assert.Fail($"{candidateFile} does not exist so cannot compare it with {truthFile}")
            elif not <| File.Exists(truthFile) then
                let content = File.ReadAllText(candidateFile)
                Console.WriteLine("\nThe output is:")
                Console.Write(content)
                Assert.Fail($"{truthFile} does not exist so cannot compare it with {candidateFile}")
            else x.CompareContents truthFile candidateFile

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

type DirectoryComparator (fc : FileComparator) =
    let c = fc :> IComparator

    interface IComparator with
        member x.Compare truthPath candidatePath =
            walk_through_copy truthPath candidatePath c.Compare

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
        let runCommand = config path outPath
        printfn $"TEST run with: ringen {runCommand}"
        Assert.Zero(ConsoleRunner.main(Regex("\s+").Split(runCommand)), "Congiguration run halted with an error")
        let targetPath = x.RealGeneratedPath outPath
        let gold = x.GoldPath path
        c.Compare gold targetPath

type FileTester (fc : FileComparator, fileFolder) =
    inherit Tester<path * string>(fc)

    let ringenFolder = Path.GetDirectoryName(__SOURCE_DIRECTORY__)
    let testsFolder = Path.Join(ringenFolder, fileFolder)

    override x.FullPath fe =
        let name, postfix = fe
        Path.Join(testsFolder, name), postfix
    override x.OutputPath fe =
        let path, postfix = fe
        Path.ChangeExtension(path, postfix + ".generated.smt2")
    override x.GoldPath  fe =
        let path, postfix = fe
        Path.ChangeExtension(path, postfix + ".gold.smt2")
    override x.RealGeneratedPath path = path

    member x.RunTest name postfix config =
        x.Test (name, postfix) (fun (path, _) -> config path)

    member x.RunSolver name postfix timelimit (solver : Program) =
        let (origPath, _) as path = x.FullPath(name, postfix)
        let outPath = x.OutputPath path
        Options.SECONDS_TIMEOUT <- timelimit
        match solver.Run origPath (Some outPath) with
        | None -> Assert.Fail("Congiguration run halted with an error")
        | Some targetPath ->
        let gold = x.GoldPath path
        x.Compare gold targetPath

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
