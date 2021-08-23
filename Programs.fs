module RInGen.Programs
open System
open System.Diagnostics
open System.Text
open System.IO

[<AbstractClass>]
type Program () =
    abstract RunOnFile : path -> path -> bool
    abstract TargetPath : path -> path
    abstract FileExtension : string
    default x.FileExtension = ".smt2"

    abstract IsExtensionOK : string -> bool
    default x.IsExtensionOK ext = ext = x.FileExtension

    member x.SaveFile dst (lines : string list) =
        let path = Path.ChangeExtension(dst, x.FileExtension)
        Directory.CreateDirectory(Path.GetDirectoryName(dst)) |> ignore
        File.WriteAllLines(path, lines)

    member private x.CheckedRunOnFile (path : path) path' =
        if x.IsExtensionOK <| Path.GetExtension(path) then x.RunOnFile path path' else false

    member x.Run (path : path) (outputPath : path option) =
        match () with
        | _ when File.Exists(path) ->
            let filename' = Path.ChangeExtension(Path.GetFileName(path), $"""%s{x.TargetPath ""}%s{Path.GetExtension(path)}""")
            let path' =
                match outputPath with
                | Some outputDirectory when Path.EndsInDirectorySeparator(outputDirectory) -> Path.Combine(outputDirectory, filename')
                | Some outputPath -> outputPath
                | None -> Path.Combine(Path.GetDirectoryName(path), filename')
            File.Delete(path')
            if x.CheckedRunOnFile path path' then Some path' else None
        | _ when Directory.Exists(path) ->
            let directory' = x.TargetPath(Path.GetFileName(path))
            let path' =
                match outputPath with
                | Some outputDirectory when Path.EndsInDirectorySeparator(outputDirectory) -> Path.Combine(outputDirectory, directory')
                | Some outputPath -> failwith_verbose $"Trying to write directory to the file $s{outputPath}"
                | None -> Path.Combine(Path.GetDirectoryName(path), directory')
            walk_through_copy path path' (fun path path' -> x.CheckedRunOnFile path path' |> ignore)
            Some path'
        | _ -> failwith_verbose $"There is no such file or directory: %s{path}"

[<AbstractClass>]
type ProgramRunner () =
    inherit Program()

    abstract ShouldSearchForBinaryInEnvironment : bool
    abstract BinaryOptions : path -> string
    abstract BinaryName : string

    member private x.WorkingDirectory (filename : path) =
        if x.ShouldSearchForBinaryInEnvironment
            then Environment.GetEnvironmentVariable(x.BinaryName)
            else filename
        |> Path.GetDirectoryName

    member private x.SetupProcess (psinfo : ProcessStartInfo) filename =
        let executable = Option.defaultValue x.BinaryName <| Dictionary.tryGetValue x.BinaryName psinfo.Environment
        let arguments = x.BinaryOptions filename
        let statisticsFile = Path.GetTempFileName()
        psinfo.FileName <- "/usr/bin/time"
        psinfo.Arguments <- $"--quiet --output=%s{statisticsFile} --format %%M,%%e %s{executable} %s{arguments}"
        psinfo.WorkingDirectory <- x.WorkingDirectory filename
        statisticsFile

    member x.RunProcessOn (srcPath : path) =
        use p = new Process()
        p.StartInfo.RedirectStandardOutput <- true
        p.StartInfo.RedirectStandardError <- true
        p.StartInfo.UseShellExecute <- false
        p.StartInfo.CreateNoWindow <- true
        p.StartInfo.WindowStyle <- ProcessWindowStyle.Hidden
        let error = StringBuilder()
        let output = StringBuilder()
        p.ErrorDataReceived.Add(fun e -> error.AppendLine(e.Data) |> ignore)
        p.OutputDataReceived.Add(fun o -> output.AppendLine(o.Data) |> ignore)
        let statisticsFile = x.SetupProcess p.StartInfo srcPath

        p.Start() |> ignore
        p.BeginOutputReadLine()                     // output is read asynchronously
        p.BeginErrorReadLine()                      // error is read asynchronously: if we read both stream synchronously, deadlock is possible
                                                    // see: https://docs.microsoft.com/en-us/dotnet/api/system.diagnostics.processstartinfo.redirectstandardoutput?view=net-5.0#code-try-4
        let hasFinished = p.WaitForExit(MSECONDS_TIMEOUT ())
        if not hasFinished then p.Kill(true)
        p.Close()
        let error = error.ToString().Trim()
        let output = output.ToString().Trim()
        statisticsFile, hasFinished, error, output
