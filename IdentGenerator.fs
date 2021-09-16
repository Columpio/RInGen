module RInGen.IdentGenerator

open System.Collections.Generic
open System.Text.RegularExpressions

type Counter () =
    let mutable counter = -1

    member x.Count () =
        counter <- counter + 1
        counter

type IdentGenerator() =
    let symbols = Dictionary<string, int>()

    member x.gensymp prefix =
        let prefixStr = prefix.ToString()
        let prefixStr = Regex.Replace(prefixStr, "[^a-zA-Z]", "")
        let prefixStr = if prefixStr = "" then "x" else prefixStr
        let prefixStrLow = prefixStr.ToLower()
        let counter = ref 0
        if symbols.TryGetValue(prefixStrLow, counter) then
            symbols.[prefixStrLow] <- !counter + 1
        else
            symbols.Add(prefixStrLow, 1)
        $"%s{prefixStr}_%d{!counter}"

let private idgen = IdentGenerator()

let gensymp prefix = idgen.gensymp prefix
let gensym () = gensymp "x"
