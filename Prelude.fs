[<AutoOpen>]
module RInGen.Prelude
open SMTLIB2
open System.IO

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

module FileSystem =
    let isDirectory path =
        if File.Exists(path) then File.GetAttributes(path).HasFlag(FileAttributes.Directory)
        else Directory.CreateDirectory(path) |> ignore; true

    type tmpFileConfig = {namer: (unit -> string) option; outputDir: path option; extension: string option}
    let createTempFile (config : tmpFileConfig) =
        let outputDir =
            match config.outputDir with
            | Some outputDirectory when isDirectory outputDirectory -> outputDirectory
            | _ -> Path.GetTempPath()
        let outputName =
            match config.namer with
            | Some namer -> namer
            | None -> fun () -> Path.GetFileNameWithoutExtension(Path.GetTempFileName())
        let ext =
            match config.extension with
            | Some ext -> ext
            | None -> "tmp"
        fun () -> Path.Combine(outputDir, $"{outputName ()}.{ext}")

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

type atom =
    | Bot
    | Top
    | Equal of term * term
    | Distinct of term * term
    | AApply of operation * term list
    override x.ToString() =
        match x with
        | Bot -> "false"
        | Top -> "true"
        | Equal(t1, t2) -> $"(= {t1} {t2})"
        | Distinct(t1, t2) -> $"(not (= {t1} {t2}))"
        | AApply(op, []) -> op.ToString()
        | AApply(op, ts) -> sprintf "(%O %s)" op (ts |> List.map toString |> join " ")

type 'a conjunction = Conjunction of 'a list
type 'a disjunction = Disjunction of 'a list
type dnf = atom conjunction disjunction
type cnf = atom disjunction conjunction

type conditional<'a> = atom list * 'a

module Conditional =
    let toString ((conds, a) : 'a conditional) =
        let a = a.ToString()
        match conds with
        | [] -> a
        | [c] -> $"(=> %O{c} {a})"
        | _ -> $"""(=> (and {conds |> List.map toString |> join " "}) {a})"""

type rule =
    | Rule of quantifiers * atom list * atom
    override x.ToString() =
        let ruleToString ruleSymbol qs xs x =
            match xs with
            | [] -> $"{x}"
            | [y] -> $"({ruleSymbol} {y}\n\t    {x})"
            | _ -> $"""({ruleSymbol}{"\t"}(and {xs |> List.map toString |> join "\n\t\t\t"}){"\n\t\t"}{x})"""
            |> Quantifiers.toString qs
        match x with
        | Rule(qs, xs, x) -> ruleToString "=>" qs xs x

type folFormula =
    | FOLAtom of atom
    | FOLNot of folFormula
    | FOLOr of folFormula list
    | FOLAnd of folFormula list
    | FOLEq of folFormula * folFormula
    override x.ToString() =
        match x with
        | FOLAtom a -> a.ToString()
        | FOLNot a -> $"(not {a})"
        | FOLOr ats ->
            match List.choose2 (function FOLNot n -> Choice2Of2 n | a -> Choice1Of2 a) ats with
            | [head], [] -> toString head
            | [head], [body] -> $"(=> {body} {head})"
            | [head], body -> $"""(=> (and {body |> List.map toString |> join " "}) {head})"""
            | _ -> $"""(or {ats |> List.map toString |> join " "})"""
        | FOLAnd ats -> $"""(and {ats |> List.map toString |> join " "})"""
        | FOLEq(a, b) -> $"(= {a} {b})"

type lemma = quantifiers * folFormula conditional

module Lemma =
    let toString ((qs, cond) : lemma) =
        Conditional.toString cond |> Quantifiers.toString qs

let notMapApply f z = function
    | Bot -> z Top
    | Top -> z Bot
    | Equal(t1, t2) -> z <| Distinct(t1, t2)
    | Distinct(t1, t2) -> z <| Equal(t1, t2)
    | AApply(op, ts) -> f op ts

type transformedCommand =
    | OriginalCommand of command
    | TransformedCommand of rule
    | LemmaCommand of symbol * sorted_var list * lemma * lemma // body lemma, head cube
    override x.ToString() =
        match x with
        | OriginalCommand x -> x.ToString()
        | TransformedCommand x -> $"(assert %O{x})"
        | LemmaCommand(pred, vars, bodyLemma, headCube) ->
            Lemma.toStringCommand pred vars (join " " [Lemma.toString bodyLemma; Lemma.toString headCube])

type folCommand =
    | FOLOriginalCommand of command
    | FOLAssertion of quantifiers * folFormula
    override x.ToString() =
        match x with
        | FOLOriginalCommand x -> x.ToString()
        | FOLAssertion(qs, x) -> $"(assert %s{Quantifiers.toString qs x})"
