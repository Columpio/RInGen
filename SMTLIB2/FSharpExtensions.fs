[<AutoOpen>]
module SMTLIB2.FSharpExtensions
open System.Collections.Generic
open System.IO
open System.Text.RegularExpressions
open System.Threading
open System.Threading.Tasks

let __notImplemented__() = failwith "Not implemented!"
let __unreachable__() = failwith "Unreachable!"

module ThisProcess =
    let thisDLLPath = System.Reflection.Assembly.GetExecutingAssembly().Location
    let thisProcess = System.Diagnostics.Process.GetCurrentProcess()

module Printf =
    let printfn_nonempty s = if s <> "" then printfn $"%s{s}"
    let eprintfn_nonempty s = if s <> "" then eprintfn $"%s{s}"

module String =
    let inline private mapFirstChar x f = if x = "" then "" else $"%c{f(x.Chars(0))}%s{x.Substring(1)}"
    let inline toLowerFirstChar x = mapFirstChar x System.Char.ToLower
    let inline toUpperFirstChar x = mapFirstChar x System.Char.ToUpper

    let inline hasLetters (s : string) = Regex("[a-zA-Z]").IsMatch(s)

[<Struct>]
type OptionalBuilder =
    member __.Bind(opt, binder) = Option.bind binder opt
    member __.Return(value) = Some value
    member __.ReturnFrom(value) = value
    member __.Zero() = None
    member __.Using(resource : #System.IDisposable, binder) = let result = binder resource in resource.Dispose(); result
let opt = OptionalBuilder()

let inline join s (xs : string seq) = System.String.Join(s, xs)
let inline split (c : string) (s : string) = s.Split(c.ToCharArray()) |> List.ofArray
let inline fst3 (a, _, _) = a
let inline snd3 (_, a, _) = a
let inline thd3 (_, _, a) = a
let inline toString x = x.ToString()

module Int32 =
    let TryParse (s : string) =
        let n = ref 0
        if System.Int32.TryParse(s, n) then Some n.Value else None
module Int64 =
    let TryParse (s : string) =
        let n = ref 0L
        if System.Int64.TryParse(s, n) then Some n.Value else None

type Async with
    static member AwaitTask (t : Task<'T>, timeout : int) =
        async {
            use cts = new CancellationTokenSource()
            use timer = Task.Delay (timeout, cts.Token)
            let! completed = Async.AwaitTask <| Task.WhenAny(t, timer)
            if completed = (t :> Task) then
                cts.Cancel ()
                let! result = Async.AwaitTask t
                return Some result
            else return None
        }

module Map =
    let union x y = Map.foldBack Map.add x y

    let findOrDefault map x = Map.tryFind x map |> Option.defaultValue x

    let findOrApply f map x = Map.tryFind x map |> Option.defaultWith (fun () -> f x)

    let findOrAdd f x map =
        match Map.tryFind x map with
        | Some y -> y, map
        | None ->
            let y = f x
            y, Map.add x y map

module Dictionary =
    let ofList l = Dictionary(List.map KeyValuePair.Create l)

    let toList (d : IDictionary<_,_>) = d |> List.ofSeq |> List.map (fun kvp -> kvp.Key, kvp.Value)

    let copy (d : IDictionary<_,_>) = Dictionary<_, _>(d)

    let copyContents (toD : IDictionary<_,_>) (fromD : IDictionary<_,_>) = Seq.iter toD.Add fromD

    let tryFind (key : 'key) (d : IDictionary<'key, 'value>) =
        let dummy = ref Unchecked.defaultof<'value>
        if d.TryGetValue(key, dummy) then Some dummy.Value else None

    let findOrApply f map x = tryFind x map |> Option.defaultWith (fun () -> f x)

    let getOrInitWith (key : 'key) (d : IDictionary<'key, 'value>) (init : unit -> 'value) =
        match tryFind key d with
        | Some value -> value
        | None ->
            let value = init ()
            d.Add(key, value)
            value

module List =
    let cons x xs = x :: xs

    let unique xs = xs |> Set.ofList |> Set.toList

    let notEmpty xs = not (List.isEmpty xs)

    let groups n ys =
        // for [x0; x1; x2; x3; ...] and n=2 returns [[x0, x1]; [x2, x3]; ...]
        let l = List.length ys
        if l % n <> 0 then failwithf $"list %O{ys} length is not dividable by %d{n}" else
        List.splitInto (l / n) ys

    let addLast y xs =
        let rec addLast xs k =
            match xs with
            | [] -> k [y]
            | x::xs -> addLast xs (fun ys -> k <| x::ys)
        addLast xs id

    let uncons = function
        | [] -> failwith "uncons of empty list"
        | x::xs -> x, xs

    let countWith p = List.fold (fun count x -> if p x then count + 1 else count) 0

    let choose2 p xs =
        let rec choose2 xs yes nos =
            match xs with
            | [] -> List.rev yes, List.rev nos
            | x::xs ->
                match p x with
                | Choice1Of2 y -> choose2 xs (y::yes) nos
                | Choice2Of2 n -> choose2 xs yes (n::nos)
        choose2 xs [] []

    let rec foldChoose f z xs =
        match xs with
        | [] -> Some z
        | x::xs ->
            match f z x with
            | Some y -> foldChoose f y xs
            | None -> None

    let mapChoose f xs = foldChoose (fun ys x -> match f x with Some y -> Some(y::ys) | None -> None) [] xs |> Option.map List.rev

    let kfoldk f =
        let rec kfoldk z xs k =
            match xs with
            | [] -> k z
            | x::xs -> f z x (fun y -> kfoldk y xs k)
        kfoldk

    let instantiate map = List.map (Map.findOrDefault map)

    let butLast xs =
        let first, last = List.splitAt (List.length xs - 1) xs
        first, List.exactlyOne last

    let mapReduce f xs =
        match xs with
        | [] -> __unreachable__()
        | x::xs -> List.mapFold f x xs

    let mapReduceBack f xs =
        match xs with
        | [] -> __unreachable__()
        | _ ->
            let xs, x = butLast xs
            List.mapFoldBack f xs x

    let triangle xs =
        let rec iter x = function
            | [] -> []
            | y::ys as rest -> List.map (fun z -> x, z) rest @ iter y ys
        match xs with
        | [] -> __unreachable__()
        | x::xs -> iter x xs

    let product2 xs ys = List.collect (fun y -> List.map (fun x -> x, y) xs) ys

    let product xss =
        let rec product xss k =
            match xss with
            | [] -> k [[]]
            | xs::xss -> product xss (fun yss -> List.collect (fun ys -> List.map (fun x -> x :: ys) xs) yss |> k)
        product xss id

    let transpose xss =
        let uncons = List.choose (function x::xs -> Some(x, xs) | [] -> None) >> List.unzip
        let rec transpose xss =
            match uncons xss with
            | [], [] -> []
            | xs, xss -> xs :: transpose xss
        transpose xss

    let rec suffixes xs = seq {
        match xs with
        | [] -> yield []
        | _::ys ->
            yield xs
            yield! suffixes ys
    }

    let prefixes xs = xs |> List.rev |> suffixes |> List.ofSeq |> List.rev

    let initial xs = List.take (List.length xs - 1) xs

    let chunkBySecond xs =
        let d = Dictionary<_, _>()
        for f, s in xs do
            match Dictionary.tryFind s d with
            | Some fs -> d.[s] <- f::fs
            | None -> d.Add(s, [f])
        Dictionary.toList d

module Counter =
    let empty : Map<'a, int> = Map.empty

    let addMany x m c =
        match Map.tryFind x c with
        | Some n -> Map.add x (n + m) c
        | None -> Map.add x m c

    let add x c = addMany x 1 c

    let union cBig cSmall = Map.foldBack addMany cSmall cBig

    let unionMany cs = List.fold union empty cs

module Numbers =
    let allNumbersBaseM n m =
        // little-endian e.g. allNumbersBaseM 2 2 = [0; 0] [1;0] [0; 1] [1; 1]
        let rec f n m acc =
            match n with
            | 0 -> acc
            | _ ->
                let helper = f (n-1) m
                let iList = List.init m (fun i -> i::acc)
                iList |> List.map helper |> List.concat
        if n = 0 then [] else List.chunkBySize n (f n m [])

module Seq =
    let rec nondiag = function
        | [] -> Seq.empty
        | x::xs ->
            seq {
                yield! Seq.map (fun y -> x, y) xs
                yield! Seq.map (fun y -> y, x) xs
                yield! nondiag xs
            }

module Environment =
    let split (s : string) = split System.Environment.NewLine s
    let join (xs : string list) = join System.Environment.NewLine xs

exception NotSupported
