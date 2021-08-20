[<AutoOpen>]
module RInGen.Prelude
open System.Collections.Generic
open System.IO
open System.Threading
open System.Threading.Tasks

let __notImplemented__() = failwith "Not implemented!"
let __unreachable__() = failwith "Unreachable!"

module ThisProcess =
    let thisDLLPath = System.Reflection.Assembly.GetExecutingAssembly().Location
    let thisProcess = System.Diagnostics.Process.GetCurrentProcess()

let private mapFirstChar x f = if x = "" then "" else $"%c{f(x.Chars(0))}%s{x.Substring(1)}"
type System.String with
    member x.ToLowerFirstChar() = mapFirstChar x System.Char.ToLower
    member x.ToUpperFirstChar() = mapFirstChar x System.Char.ToUpper

let optCons xs = function
    | Some x -> x::xs
    | None -> xs

let rec butLast = function
    | [] -> failwith "Empty list!"
    | [_] -> []
    | x::xs -> x :: butLast xs

[<Struct>]
type OptionalBuilder =
    member __.Bind(opt, binder) =
        match opt with
        | Some value -> binder value
        | None -> None
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
let inline pair x y = x, y

let inline toString x = x.ToString()

module Int32 =
    let TryParse (s : string) =
        let n = ref 0
        if System.Int32.TryParse(s, n) then Some !n else None
module Int64 =
    let TryParse (s : string) =
        let n = ref 0L
        if System.Int64.TryParse(s, n) then Some !n else None

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

module List =
    let cons x xs = x :: xs

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

    let butLast xs =
        let first, last = List.splitAt (List.length xs - 1) xs
        first, List.head last

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

module Seq =
    let rec nondiag = function
        | [] -> Seq.empty
        | x::xs ->
            seq {
                yield! Seq.map (fun y -> x, y) xs
                yield! Seq.map (fun y -> y, x) xs
                yield! nondiag xs
            }

module Map =
    let union x y = Map.foldBack Map.add x y

module Dictionary =
    let toList (d : IDictionary<_,_>) = d |> List.ofSeq |> List.map (fun kvp -> kvp.Key, kvp.Value)

    let tryGetValue (key : 'key) (d : IDictionary<'key, 'value>) =
        let dummy = ref (Unchecked.defaultof<'value>)
        if d.TryGetValue(key, dummy) then Some !dummy else None

type path = string
type symbol = string
let symbol : string -> symbol = id
module Symbols =
    let sprintForDeclare = id

    let addPrefix (pref : string) s = pref + s
type ident = symbol
type sort =
    | PrimitiveSort of ident
    | CompoundSort of ident * sort list
    override x.ToString() =
        match x with
        | PrimitiveSort i -> i.ToString()
        | CompoundSort(name, sorts) -> sorts |> List.map toString |> join " " |> sprintf "(%s %s)" name
let (|ArraySort|_|) = function
    | CompoundSort("Array", [s1; s2]) -> Some(s1, s2)
    | _ -> None
let ArraySort(s1, s2) = CompoundSort("Array", [s1; s2])
let sortToFlatString s =
    let rec sortToFlatString = function
        | PrimitiveSort s -> [s.ToString()]
        | CompoundSort(name, sorts) -> name :: List.collect sortToFlatString sorts
    sortToFlatString s |> join ""
let boolSort = PrimitiveSort(symbol("Bool"))
let integerSort = PrimitiveSort(symbol("Int"))
let dummySort = PrimitiveSort(symbol("*dummy-sort*"))
let argumentSortsOfArraySort = function
    | ArraySort(s1, s2) -> s1, s2
    | _ -> __unreachable__()
type pattern = symbol list
type sorted_var = symbol * sort
type operation =
    | ElementaryOperation of ident * sort list * sort
    | UserDefinedOperation of ident * sort list * sort
    override x.ToString() =
        match x with
        | ElementaryOperation(s, _, _)
        | UserDefinedOperation(s, _, _) -> toString s
type smtExpr =
    | Number of int64
    | BoolConst of bool
    | Ident of ident * sort
    | Apply of operation * smtExpr list
    | Let of (sorted_var * smtExpr) list * smtExpr
    | Match of smtExpr * (smtExpr * smtExpr) list
    | Ite of smtExpr * smtExpr * smtExpr
    | And of smtExpr list
    | Or of smtExpr list
    | Not of smtExpr
    | Hence of smtExpr * smtExpr
    | Forall of sorted_var list * smtExpr
    | Exists of sorted_var list * smtExpr
    override x.ToString() =
        let term_list_to_string = List.map toString >> join " "
        let atom_list_to_string = List.map toString >> join " "
        let sorted_vars_to_string = List.map (fun (v, e) -> $"({v} {e})") >> join " "
        let bindings_to_string = List.map (fun ((v, _), e) -> $"({v} {e})") >> join " "
        match x with
        | Apply(f, xs) -> $"({f} %s{term_list_to_string xs})"
        | Number n -> toString n
        | BoolConst true -> "true"
        | BoolConst false -> "false"
        | Ident(x, _) -> x.ToString()
        | Let(bindings, body) ->
            $"(let (%s{bindings_to_string bindings}) {body})"
        | Match(t, cases) ->
            sprintf "(match %O (%s))" t (cases |> List.map (fun (pat, t) -> $"({pat} {t})") |> join " ")
        | Ite(i, t, e) -> $"(ite {i} {t} {e})"
        | And xs -> $"(and %s{atom_list_to_string xs})"
        | Or xs -> $"(or %s{atom_list_to_string xs})"
        | Not x -> $"(not {x})"
        | Hence(i, t) -> $"(=> {i} {t})"
        | Forall(vars, body) ->
            $"(forall (%s{sorted_vars_to_string vars}) {body})"
        | Exists(vars, body) ->
            $"(exists (%s{sorted_vars_to_string vars}) {body})"
type function_def = symbol * sorted_var list * sort * smtExpr
type term =
    | TConst of ident * sort
    | TIdent of ident * sort
    | TApply of operation * term list
    override x.ToString() =
        match x with
        | TConst(name, _) -> name.ToString()
        | TIdent(name, _) -> name.ToString()
        | TApply(op, []) -> op.ToString()
        | TApply(f, xs) -> sprintf "(%O %s)" f (xs |> List.map toString |> join " ")
let typeOfTerm = function
    | TConst(_, typ)
    | TIdent(_, typ)
    | TApply(ElementaryOperation(_, _, typ), _)
    | TApply(UserDefinedOperation(_, _, typ), _) -> typ
type atom =
    | Top
    | Bot
    | Equal of term * term
    | Distinct of term * term
    | AApply of operation * term list
    override x.ToString() =
        match x with
        | Top -> "true"
        | Bot -> "false"
        | Equal(t1, t2) -> $"(= {t1} {t2})"
        | Distinct(t1, t2) -> $"(not (= {t1} {t2}))"
        | AApply(op, []) -> op.ToString()
        | AApply(op, ts) -> sprintf "(%O %s)" op (ts |> List.map toString |> join " ")
type rule =
    | BaseRule of atom list * atom
    | ForallRule of sorted_var list * rule
    | ExistsRule of sorted_var list * rule
    override x.ToString() =
        let quant quantName vars = if List.isEmpty vars then id else vars |> List.map (fun (v, e) -> $"({v} {e})") |> join " " |> sprintf "(%s (%s)\n\t%s)" quantName
        let rec basicPrint x =
            match x with
            | BaseRule(xs, x) ->
                match xs with
                | [] -> $"{x}"
                | [y] -> $"(=> {y}\n\t    {x})"
                | _ -> sprintf "(=>\t(and %s)\n\t\t%O)" (xs |> List.map toString |> join "\n\t\t\t") x
            | ForallRule(vars, body) -> quant "forall" vars (basicPrint body)
            | ExistsRule(vars, body) -> quant "exists" vars (basicPrint body)
        basicPrint x
let rec forallrule = function
    | [] -> id
    | vars -> function
        | ForallRule(vars', body) -> forallrule (vars @ vars') body
        | body -> ForallRule(vars, body)
let rec existsrule = function
    | [] -> id
    | vars -> function
        | ExistsRule(vars', body) -> existsrule (vars @ vars') body
        | body -> ExistsRule(vars, body)
let aerule forallVars existsVars fromatoms toatom = forallrule forallVars (existsrule existsVars (BaseRule(fromatoms, toatom)))
let rule vars fromatoms toatom = forallrule vars (BaseRule(fromatoms, toatom))
let (|Rule|_|) = function
    | ForallRule(vars, BaseRule(f, t)) -> Some(vars, f, t)
    | BaseRule(f, t) -> Some([], f, t)
    | _ -> None
let private sorted_var_to_string = List.map (fun (v, s) -> $"({v} {s})") >> join " "
type definition =
    | DefineFun of function_def
    | DefineFunRec of function_def
    | DefineFunsRec of function_def list
    override x.ToString() =
        match x with
        | DefineFunRec(name, vars, returnType, body) ->
            $"(define-fun-rec {Symbols.sprintForDeclare name} (%s{sorted_var_to_string vars}) {returnType} {body})"
        | DefineFun(name, vars, returnType, body) ->
            $"(define-fun {Symbols.sprintForDeclare name} (%s{sorted_var_to_string vars}) {returnType} {body})"
        | DefineFunsRec fs ->
            let signs, bodies = List.map (fun (n, vs, s, b) -> (n, vs, s), b) fs |> List.unzip
            let signs = signs |> List.map (fun (name, vars, sort) -> $"(%s{Symbols.sprintForDeclare name} (%s{sorted_var_to_string vars}) {sort})") |> join " "
            let bodies = bodies |> List.map toString |> join " "
            $"(define-funs-rec (%s{signs}) (%s{bodies}))"
type command =
    | CheckSat
    | GetModel
    | Exit
    | GetInfo of string
    | GetProof
    | SetInfo of string * string option
    | SetLogic of string
    | SetOption of string
    | DeclareDatatype of sort * (symbol * sorted_var list) list
    | DeclareDatatypes of (sort * (symbol * sorted_var list) list) list
    | DeclareFun of symbol * sort list * sort
    | DeclareSort of sort
    | DeclareConst of symbol * sort
    override x.ToString() =
        let constrs_to_string =
            List.map (fun (c, args) -> $"({c} %s{sorted_var_to_string args})") >> join " " >> sprintf "(%s)"
        let dtsToString dts =
            let sorts, decs = List.unzip dts
            let sorts = sorts |> List.map (sprintf "(%O 0)") |> join " "
            sprintf "(declare-datatypes (%s) (%s))" sorts (decs |> List.map constrs_to_string |> join " ")
        match x with
        | Exit -> "(exit)"
        | CheckSat -> "(check-sat)"
        | GetModel -> "(get-model)"
        | GetProof -> "(get-proof)"
        | GetInfo s -> $"(get-info %s{s})"
        | SetInfo(k, vopt) -> $"""(set-info %s{k} %s{Option.defaultValue "" vopt})"""
        | SetLogic l -> $"(set-logic %s{l})"
        | SetOption l -> $"(set-option %s{l})"
        | DeclareConst(name, sort) -> $"(declare-const {name} {sort})"
        | DeclareSort sort -> $"(declare-sort {sort} 0)"
        | DeclareFun(name, args, ret) -> sprintf "(declare-fun %s (%s) %O)" (Symbols.sprintForDeclare name) (args |> List.map toString |> join " ") ret
        | DeclareDatatype(name, constrs) -> dtsToString [name, constrs]
            // sprintf "(declare-datatype %O %s)" name (constrs_to_string constrs)
        | DeclareDatatypes dts -> dtsToString dts
type originalCommand =
    | Definition of definition
    | Command of command
    | Assert of smtExpr
    override x.ToString() =
        match x with
        | Definition df -> df.ToString()
        | Command cmnd -> cmnd.ToString()
        | Assert f -> $"(assert {f})"
type transformedCommand =
    | OriginalCommand of command
    | TransformedCommand of rule
    override x.ToString() =
        match x with
        | OriginalCommand x -> x.ToString()
        | TransformedCommand x -> $"(assert %O{x})"
let orig = OriginalCommand
let trans = TransformedCommand
let truee = BoolConst true
let falsee = BoolConst false
let truet = TConst("true", boolSort)
let falset = TConst("false", boolSort)
let boolToConst b = if b then truet else falset
let intToConst n = TConst(toString n, integerSort)
let distinct t1 t2 =
    match t1, t2 with
    | TConst("true", _), TConst("true", _) -> Bot
    | TConst("true", _), TConst("false", _) -> Top
    | TConst("false", _), TConst("true", _) -> Top
    | TConst("false", _), TConst("false", _) -> Bot
    | t, TConst("false", _)
    | TConst("false", _), t -> Equal(t, truet)
    | t, TConst("true", _)
    | TConst("true", _), t -> Equal(t, falset)
    | _ -> Distinct(t1, t2)
let ore =
    let rec ore acc = function
        | [] ->
            match acc with
            | [] -> falsee
            | [t] -> t
            | ts -> Or <| List.rev ts
        | BoolConst true :: _ -> truee
        | BoolConst false :: xs -> ore acc xs
        | x :: xs -> ore (x :: acc) xs
    ore []
let ande =
    let rec ande acc = function
        | [] ->
            match acc with
            | [] -> truee
            | [t] -> t
            | ts -> And <| List.rev ts
        | BoolConst false :: _ -> falsee
        | BoolConst true :: xs -> ande acc xs
        | x :: xs -> ande (x :: acc) xs
    ande []
let hence ts t =
    match ts with
    | [] -> t
    | [ts] -> Hence(ts, t)
    | _ -> Hence(ande ts, t)
let rec note = function
    | BoolConst b -> b |> not |> BoolConst
    | Not e -> simplee e
    | Hence(a, b) -> ande [simplee a; note b]
    | And es -> es |> List.map note |> ore
    | Or es -> es |> List.map note |> ande
    | Exists(vars, body) -> Forall(vars, note body)
    | Forall(vars, body) -> Exists(vars, note body)
    | e -> Not e
and private simplee = function
    | Not (Not e) -> simplee e
    | Not e -> note e
    | And e -> ande e
    | Or e -> ore e
    | e -> e
let forall vars e = if List.isEmpty vars then e else Forall(vars, e)
let exists vars e = if List.isEmpty vars then e else Exists(vars, e)

type 'a conjunction = Conjunction of 'a list
type 'a disjunction = Disjunction of 'a list
type dnf = atom conjunction disjunction
type cnf = atom disjunction conjunction

module Conj =
    let singleton x = Conjunction [x]
    let exponent (Conjunction cs : 'a disjunction conjunction) : 'a conjunction disjunction =
        List.map (function Disjunction cs -> cs) cs |> List.product |> List.map Conjunction |> Disjunction
    let map produce_disjunction (Conjunction dss) =
        List.map (produce_disjunction >> Disjunction) dss |> Conjunction
    let bind (produce_disjunction : atom -> atom list) =
        map (function Disjunction ds -> List.collect produce_disjunction ds)
    let flatten (Conjunction css : 'a conjunction conjunction) = List.collect (function Conjunction cs -> cs) css |> Conjunction

module Disj =
    let singleton x = Disjunction [x]
    let get (Disjunction d) = d
    let map f (Disjunction ds) = List.map f ds |> Disjunction
    let exponent (Disjunction cs : 'a conjunction disjunction) : 'a disjunction conjunction =
        List.map (function Conjunction cs -> cs) cs |> List.product |> List.map Disjunction |> Conjunction
    let disj dss = List.collect (function Disjunction ds -> ds) dss |> Disjunction
    let conj (dss : 'a conjunction disjunction list) =
        let css = Conj.exponent (Conjunction dss)
        let cs = map Conj.flatten css
        cs
    let union (Disjunction d1) (Disjunction d2) = Disjunction (d1 @ d2)

module DNF =
    let empty : dnf = Disjunction [Conjunction []]
    let singleton : atom -> dnf = Conj.singleton >> Disj.singleton
    let flip (Disjunction cs : dnf) : cnf = cs |> List.map (function Conjunction cs -> Disjunction cs) |> Conjunction

[<Struct>]
type CollectBuilder =
    member __.Bind(xs, binder) = List.collect binder xs
    member __.Bind(Disjunction dss : dnf, binder) = List.collect (function Conjunction cs -> binder cs) dss
    member __.Return(value) = [value]
    member __.ReturnFrom(value) = value
let collector = CollectBuilder()

let private walk_through (srcDir : path) targetDir gotoFile gotoDirectory transform =
    let rec walk sourceFolder destFolder =
        for file in Directory.GetFiles(sourceFolder) do
            let name = Path.GetFileName(file)
            let dest = gotoFile destFolder name
            transform file dest
        for folder in Directory.GetDirectories(sourceFolder) do
            let name = Path.GetFileName(folder)
            let dest = gotoDirectory destFolder name
            walk folder dest
    walk srcDir targetDir

let walk_through_copy srcDir targetDir transform =
    let gotoFile folder name = Path.Combine(folder, name)
    let gotoDirectory folder name =
            let dest = Path.Combine(folder, name)
            Directory.CreateDirectory(dest) |> ignore
            dest
    walk_through srcDir targetDir gotoFile gotoDirectory transform

let walk_through_relative srcDir transform =
    let gotoInside folder name = Path.Combine(folder, name)
    walk_through srcDir "" gotoInside gotoInside (fun _ -> transform)

let walk_through_simultaneously originalDir transAndResultDirs transform =
    let addPathFragment fragment (dir1, dir2) = Path.Combine(dir1, fragment), Path.Combine(dir2, fragment)
    let rec walk relName (baseDir : DirectoryInfo) (dirs : (path * path) list) =
        for f in baseDir.EnumerateFiles() do
            let fileName = f.Name
            let relName = Path.Combine(relName, fileName)
            let files = dirs |> List.map (addPathFragment fileName)
            transform relName files
        for subDir in baseDir.EnumerateDirectories() do
            let subDirName = subDir.Name
            let subDirs = dirs |> List.map (addPathFragment subDirName)
            walk (Path.Combine(relName, subDirName)) subDir subDirs
    walk "" (Directory.CreateDirectory(originalDir)) transAndResultDirs

module Environment =
    let split (s : string) = split System.Environment.NewLine s

exception NotSupported
