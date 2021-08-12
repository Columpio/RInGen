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

    member private x.RunOnDirectory path =
        let path' = x.TargetPath path
        walk_through_copy path path' (fun path path' -> x.CheckedRunOnFile path path' |> ignore)
        Some path'

    member x.Run(path : path) =
        match () with
        | _ when File.Exists(path) ->
            let path' = Path.ChangeExtension(path, $"""%s{x.TargetPath ""}%s{Path.GetExtension(path)}""")
            if x.CheckedRunOnFile path path' then Some path' else None
        | _ when Directory.Exists(path) -> x.RunOnDirectory(path)
        | _ -> failwith_verbose $"There is no such file or directory: %s{path}"
