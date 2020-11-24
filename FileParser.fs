module RInGen.FileParser
open System.IO
open Lexer


let parse_file filename =
    let text = sprintf "(%s)" <| File.ReadAllText(filename)
    try
        let (PList exprs) = parse_string text
        exprs
    with _ -> printfn "%s" filename; reraise ()
