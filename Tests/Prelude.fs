namespace Tests
open NUnit.Framework

[<SetUpFixture>]
type SetupTrace () =
    let out = System.Console.Out

    [<OneTimeSetUp>]
    member x.StartTest () =
        System.Console.SetOut(TestContext.Progress)

    [<OneTimeTearDown>]
    member x.StopTest () =
        System.Console.SetOut(out)
