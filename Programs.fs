[<AutoOpen>]
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

    static member SaveFile (dst : path) (lines : string list) =
        Directory.CreateDirectory(Path.GetDirectoryName(dst)) |> ignore
        File.WriteAllLines(dst, lines)

    member private x.CheckedRunOnFile (path : path) path' =
        if x.IsExtensionOK <| Path.GetExtension(path) then x.RunOnFile path (Path.ChangeExtension(path', x.FileExtension)) else false

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

    let error = StringBuilder()
    let output = StringBuilder()

    abstract ShouldSearchForBinaryInEnvironment : bool
    abstract BinaryOptions : path -> string
    abstract BinaryName : string

    abstract HandleErrorLineReceived : string -> unit
    abstract HandleOutputLineReceived : string -> unit
    default x.HandleErrorLineReceived line = error.AppendLine(line) |> ignore
    default x.HandleOutputLineReceived line = output.AppendLine(line) |> ignore
    abstract ErrorReceived : unit -> string
    abstract OutputReceived : unit -> string
    default x.ErrorReceived () = error.ToString()
    default x.OutputReceived () = output.ToString()
    abstract ResetErrorReceiver : unit -> unit
    abstract ResetOutputReceiver : unit -> unit
    default x.ResetErrorReceiver () = error.Clear() |> ignore
    default x.ResetOutputReceiver () = output.Clear() |> ignore

    member private x.WorkingDirectory (filename : path) =
        if x.ShouldSearchForBinaryInEnvironment
            then Environment.GetEnvironmentVariable(x.BinaryName)
            else filename
        |> Path.GetDirectoryName

    member private x.SetupProcess (psinfo : ProcessStartInfo) filename =
        let executable = Option.defaultValue x.BinaryName <| Dictionary.tryGetValue x.BinaryName psinfo.Environment
        let arguments = x.BinaryOptions filename
        let statisticsFile = Path.GetTempFileName()
        File.Delete(statisticsFile)
        psinfo.FileName <- "/usr/bin/time"
        psinfo.Arguments <- $"--quiet --output=%s{statisticsFile} --format %%M,%%e %s{executable} %s{arguments}"
        print_verbose $"Run: %s{psinfo.FileName} %s{psinfo.Arguments}"
        psinfo.WorkingDirectory <- x.WorkingDirectory filename
        executable, statisticsFile

    member x.RunProcessOn (srcPath : path) =
        x.ResetErrorReceiver ()
        x.ResetOutputReceiver ()
        use p = new Process()
        p.StartInfo.RedirectStandardOutput <- true
        p.StartInfo.RedirectStandardError <- true
        p.StartInfo.UseShellExecute <- false
        p.StartInfo.CreateNoWindow <- true
        p.StartInfo.WindowStyle <- ProcessWindowStyle.Hidden
        p.ErrorDataReceived.Add(fun e -> x.HandleErrorLineReceived e.Data)
        p.OutputDataReceived.Add(fun o -> x.HandleOutputLineReceived o.Data)
        let executable, statisticsFile = x.SetupProcess p.StartInfo srcPath

        p.Start() |> ignore
        p.BeginOutputReadLine()                     // output is read asynchronously
        p.BeginErrorReadLine()                      // error is read asynchronously: if we read both stream synchronously, deadlock is possible
                                                    // see: https://docs.microsoft.com/en-us/dotnet/api/system.diagnostics.processstartinfo.redirectstandardoutput?view=net-5.0#code-try-4

        let st = p.StartTime
        let isChildProcess (pr : Process) =
            try
                pr.StartTime >= st && pr.ProcessName = executable
            with _ -> false
        let child_solver = Process.GetProcesses() |> List.ofArray |> List.filter isChildProcess |> List.tryHead

        let hasFinished = p.WaitForExit(MSECONDS_TIMEOUT ())
        if hasFinished then () else // p.WaitForExit() else
            try match child_solver with
                | Some child_solver -> child_solver.Kill(true)
                | _ -> p.Kill(true)
            with _ -> ()
        p.Close()
        let error = x.ErrorReceived().Trim()
        let output = x.OutputReceived().Trim()
        statisticsFile, hasFinished, error, output

type transformOptions = {tip: bool; sync_terms: bool; tta_transform:bool; child_transformer: ProgramRunner option}
type solvingOptions = {keep_exists: bool; table: bool}
type transformContext = {commands: transformedCommand list; diseqs: Map<sort, operation>}