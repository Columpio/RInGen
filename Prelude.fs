[<AutoOpen>]
module FLispy.Prelude
open System.IO

let __notImplemented__() = failwith "Not implemented!"
let __unreachable__() = failwith "Unreachable!"

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
let opt = OptionalBuilder()

[<Struct>]
type ListCollectBuilder =
    member __.Bind(xs, binder) = List.collect binder xs
    member __.Return(value) = [value]
let collector = ListCollectBuilder()

let inline join s (xs : string seq) = System.String.Join(s, xs)
let inline fst3 (a, _, _) = a
let inline snd3 (_, a, _) = a
let inline thd3 (_, _, a) = a

let inline toString x = x.ToString()

module List =
    let cons x xs = x :: xs

    let product xss =
        let rec product xss k =
            match xss with
            | [] -> k [[]]
            | xs::xss -> product xss (fun yss -> List.collect (fun ys -> List.map (fun x -> x :: ys) xs) yss |> k)
        product xss id

module Seq =
    let rec nondiag = function
        | [] -> Seq.empty
        | x::xs ->
            seq {
                yield! Seq.map (fun y -> x, y) xs
                yield! Seq.map (fun y -> y, x) xs
                yield! nondiag xs
            }


type ParseExpression =
    | PNumber of int
    | PSymbol of string
    | PList of ParseExpression list
    | PMatch of ParseExpression * (ParseExpression * ParseExpression) list
    | PComment

type symbol = string
type ident = symbol
type sort = ident
type pattern = symbol list
type constant =
    | Number of int
    | Bool of bool
    override x.ToString() =
        match x with
        | Number i -> toString i
        | Bool true -> "true"
        | Bool false -> "false"
type sorted_var = symbol * sort
type operation =
    | ElementaryOperation of string * sort list
    | UserDefinedOperation of string * sort list
    override x.ToString() =
        match x with
        | ElementaryOperation(s, _)
        | UserDefinedOperation(s, _) -> toString s
type term =
    | Constant of constant
    | Ident of ident * sort
    | Apply of operation * term list
    | Let of (symbol * term) list * term
    | Forall of sorted_var list * term
    | Exists of sorted_var list * term
    | Match of term * (term * term) list
    | Ite of term * term * term
    | And of term list
    | Or of term list
    | Not of term
    | Hence of term * term
    override x.ToString() =
        let list_to_string = List.map toString >> join " "
        let sorted_vars_to_string = List.map (fun (v, e) -> sprintf "(%O %O)" v e) >> join " "
        let bindings_to_string = List.map (fun (v, e) -> sprintf "(%O %O)" v e) >> join " "
        match x with
        | Constant c -> toString c
        | Ident(x, _) -> x
        | Apply(f, xs) -> sprintf "(%O %s)" f (list_to_string xs)
        | Let(bindings, body) ->
            sprintf "(let (%s) %O)" (bindings_to_string bindings) body
        | Forall(vars, body) ->
            sprintf "(forall (%s) %O)" (sorted_vars_to_string vars) body
        | Exists(vars, body) ->
            sprintf "(exists (%s) %O)" (sorted_vars_to_string vars) body
        | Match(t, cases) ->
            sprintf "(match %O (%s))" t (cases |> List.map (fun (pat, t) -> sprintf "(%O %O)" pat t) |> join " ")
        | Ite(i, t, e) -> sprintf "(ite %O %O %O)" i t e
        | And xs -> sprintf "(and %s)" (list_to_string xs)
        | Or xs -> sprintf "(or %s)" (list_to_string xs)
        | Not x -> sprintf "(not %O)" x
        | Hence(i, t) -> sprintf "(=> %O %O)" i t
type function_def = symbol * sorted_var list * sort * term
type command =
    | Assert of term
    | CheckSat
    | GetModel
    | GetInfo of string
    | SetLogic of string
    | DeclareDatatype of symbol * (symbol * sorted_var list) list
    | DeclareDatatypes of (symbol * (symbol * sorted_var list) list) list
    | DeclareFun of symbol * sort list * sort
    | DeclareSort of sort
    | DeclareConst of symbol * sort
    | DefineFun of function_def
    | DefineFunRec of function_def
    | DefineFunsRec of function_def list
    override x.ToString() =
        let sorted_var_to_string = List.map (fun (v, s) -> sprintf "(%O %O)" v s) >> join " "
        let constrs_to_string =
            List.map (fun (c, args) -> sprintf "(%O %s)" c (sorted_var_to_string args)) >> join " " >> sprintf "(%s)"
        match x with
        | Assert t -> sprintf "(assert %O)" t
        | CheckSat -> "(check-sat)"
        | GetModel -> "(get-model)"
        | GetInfo s -> sprintf "(get-info %s)" s
        | SetLogic l -> sprintf "(set-logic %s)" l
        | DeclareConst(name, sort) -> sprintf "(declare-const %O %O)" name sort
        | DeclareSort sort -> sprintf "(declare-sort %O 0)" sort
        | DeclareFun(name, args, ret) -> sprintf "(declare-fun %O (%s) %O)" name (args |> List.map toString |> join " ") ret
        | DeclareDatatype(name, constrs) ->
            sprintf "(declare-datatype %O %s)" name (constrs_to_string constrs)
        | DeclareDatatypes dts ->
            let sorts, decs = List.unzip dts
            let sorts = sorts |> List.map (sprintf "(%O 0)") |> join " "
            sprintf "(declare-datatypes (%s) (%s))" sorts (decs |> List.map constrs_to_string |> join " ")
        | DefineFunRec(name, vars, returnType, body) ->
            sprintf "(define-fun-rec %O (%s) %O %O)" name (sorted_var_to_string vars) returnType body
        | DefineFun(name, vars, returnType, body) ->
            sprintf "(define-fun %O (%s) %O %O)" name (sorted_var_to_string vars) returnType body
        | DefineFunsRec fs ->
            let signs, bodies = List.map (fun (n, vs, s, b) -> (n, vs, s), b) fs |> List.unzip
            let signs = signs |> List.map (fun (name, vars, sort) -> sprintf "(%O (%s) %O)" name (sorted_var_to_string vars) sort) |> join " "
            let bodies = bodies |> List.map toString |> join " "
            sprintf "(define-funs-rec (%s) (%s))" signs bodies
let truee = Constant(Bool true)
let falsee = Constant(Bool false)
let ore =
    let rec ore acc = function
        | [] ->
            match acc with
            | [] -> falsee
            | [t] -> t
            | ts -> Or <| List.rev ts
        | Constant(Bool true) :: _ -> truee
        | Constant(Bool false) :: xs -> ore acc xs
        | x :: xs -> ore (x :: acc) xs
    ore []
let ande =
    let rec ande acc = function
        | [] ->
            match acc with
            | [] -> truee
            | [t] -> t
            | ts -> And <| List.rev ts
        | Constant(Bool false) :: _ -> falsee
        | Constant(Bool true) :: xs -> ande acc xs
        | x :: xs -> ande (x :: acc) xs
    ande []

let walk_through (directory : string) postfix transform =
    let rec walk sourceFolder destFolder =
        if not <| Directory.Exists(destFolder) then
            Directory.CreateDirectory(destFolder) |> ignore
        for file in Directory.GetFiles(sourceFolder) do
            let name = Path.GetFileName(file)
            let dest = Path.Combine(destFolder, name)
            transform file dest
        for folder in Directory.GetDirectories(sourceFolder) do
            let name = Path.GetFileName(folder)
            let dest = Path.Combine(destFolder, name)
            walk folder dest
    let name' = directory + postfix
    walk directory name'
    name'

let walk_through_simultaneously dirs transform =
    let rec walk relName (baseDir : DirectoryInfo) (dirs : string list) =
        for f in baseDir.EnumerateFiles() do
            let fileName = f.Name
            let relName = Path.Combine(relName, fileName)
            let files = dirs |> List.map (fun dir -> Path.Combine(dir, fileName))
            transform relName files
        for subDir in baseDir.EnumerateDirectories() do
            let subDirName = subDir.Name
            let subDirs = dirs |> List.map (fun d -> Path.Combine(d, subDirName))
            walk (Path.Combine(relName, subDirName)) subDir subDirs
    match dirs with
    | dir::_ -> walk "" (Directory.CreateDirectory(dir)) dirs
    | [] -> __unreachable__()

module MatchExtensions =
    let getFreeVarsFromPattern typer =
        let rec get_free_vars = function
            | Apply(_, ts) -> List.collect get_free_vars ts
            | Ident(name, _) when Map.containsKey name typer -> []
            | Ident(v, t) -> [v, t]
            | _ -> __unreachable__()
        get_free_vars