module RInGen.Programs
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

    member x.Run (path : path) (outputDirectory : path option) =
        let outputDirectory = Option.defaultValue (Path.GetDirectoryName(path)) outputDirectory
        match () with
        | _ when File.Exists(path) ->
            let filename' = Path.ChangeExtension(Path.GetFileName(path), $"""%s{x.TargetPath ""}%s{Path.GetExtension(path)}""")
            let path' = Path.Combine(outputDirectory, filename')
            File.Delete(path')
            if x.CheckedRunOnFile path path' then Some path' else None
        | _ when Directory.Exists(path) ->
            let directory' = x.TargetPath(Path.GetFileName(path))
            let path' = Path.Combine(outputDirectory, directory')
            walk_through_copy path path' (fun path path' -> x.CheckedRunOnFile path path' |> ignore)
            Some path'
        | _ -> failwith_verbose $"There is no such file or directory: %s{path}"
