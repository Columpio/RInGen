module RInGen.IdentGenerator

open System.Collections.Generic
open System.Text.RegularExpressions
open RInGen.Operations

type IdentGenerator() =
    let symbols = Dictionary<string, int>()

    member x.gensymp (prefix : symbol) =
        let prefixStr = prefix.ToString()
        let prefixStr = Regex.Replace(prefixStr, "[^a-zA-Z]", "")
        let prefixStr = if prefixStr = "" then "x" else prefixStr
        let prefixStrLow = prefixStr.ToLower()
        let counter = ref 0
        if symbols.TryGetValue(prefixStrLow, counter) then
            symbols.[prefixStrLow] <- !counter + 1
        else
            symbols.Add(prefixStrLow, 1)
        sprintf "%s_%d" prefixStr !counter

let mutable idgen = IdentGenerator()

let setup () =
    idgen <- IdentGenerator()

let gensymp (prefix : symbol) = idgen.gensymp prefix
let gensyms = symbol >> gensymp
let gensym () = gensyms "x"
let gensymsort = function
    | PrimitiveSort s -> gensymp s |> PrimitiveSort
    | _ -> __unreachable__()

let generateReturnArgument op =
    let retType = Operation.returnType op
    let retArg = gensym (), retType
    let retVar = TIdent retArg
    retArg, retVar

let generateArguments = Operation.argumentTypes >> List.map (fun s -> gensym(), s)
