namespace Tests
open NUnit.Framework
open System.IO

[<SetUpFixture>]
type SetupTrace () =
    let out = System.Console.Out

    static member OverwriteGoldValues = false

    [<OneTimeSetUp>]
    member x.StartTest () =
        System.Console.SetOut(TestContext.Progress)

    [<OneTimeTearDown>]
    member x.StopTest () =
        System.Console.SetOut(out)

module File =
    let tryFindDistinctLines fn1 fn2 =
        let f1 = File.ReadLines(fn1)
        let f2 = File.ReadLines(fn2)
        Seq.zip f1 f2 |> Seq.tryFind (fun (line1, line2) -> line1 <> line2)
