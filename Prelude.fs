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

module Printf =
    let printfn_nonempty s = if s <> "" then printfn $"%s{s}"
    let eprintfn_nonempty s = if s <> "" then eprintfn $"%s{s}"

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
        let dummy = ref Unchecked.defaultof<'value>
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

    member x.getBotSymbol() =
        match x with
        | PrimitiveSort name
        | CompoundSort(name, _) ->
            sprintf "%s_bot" name

    override x.ToString() =
        match x with
        | PrimitiveSort i -> i.ToString()
        | CompoundSort(name, sorts) -> sorts |> List.map toString |> join " " |> sprintf "(%s %s)" name
let (|ArraySort|_|) = function
    | CompoundSort("Array", [s1; s2]) -> Some(s1, s2)
    | _ -> None
let ArraySort(s1, s2) = CompoundSort("Array", [s1; s2])
let boolSort = PrimitiveSort(symbol("Bool"))
let integerSort = PrimitiveSort(symbol("Int"))
let dummySort = PrimitiveSort(symbol("*dummy-sort*"))
let emptySort = PrimitiveSort(symbol(" "))

module Sort =
    let gensym = function
        | PrimitiveSort s -> IdentGenerator.gensymp s |> PrimitiveSort
        | _ -> __unreachable__()

    let argumentSortsOfArraySort = function
        | ArraySort(s1, s2) -> s1, s2
        | _ -> __unreachable__()

    let sortToFlatString s =
        let rec sortToFlatString = function
            | PrimitiveSort s -> [s.ToString()]
            | CompoundSort(name, sorts) -> name :: List.collect sortToFlatString sorts
        sortToFlatString s |> join ""

type pattern = symbol list
type sorted_var = symbol * sort

module SortedVar =
    let fresh ((v, s) : sorted_var) : sorted_var = IdentGenerator.gensymp v, s

module SortedVars =
    let mapFold = List.mapFold

    let withFreshVariables = List.mapFold (fun freshVarsMap vs -> let vs' = SortedVar.fresh vs in vs', Map.add vs vs' freshVarsMap)

    let toString : sorted_var list -> string = List.map (fun (v, s) -> $"({v} {s})") >> join " "

type operation =
    | ElementaryOperation of ident * sort list * sort
    | UserDefinedOperation of ident * sort list * sort

    member x.getSort() =
        match x with
        | ElementaryOperation(_, _, s)
        | UserDefinedOperation(_, _, s) ->
            s
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
        let bindings_to_string = List.map (fun ((v, _), e) -> $"({v} {e})") >> join " "
        match x with
        | Apply(f, []) -> f.ToString()
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
            $"(forall (%s{SortedVars.toString vars}) {body})"
        | Exists(vars, body) ->
            $"(exists (%s{SortedVars.toString vars}) {body})"
type function_def = symbol * sorted_var list * sort * smtExpr
type term =
    | TConst of ident * sort
    | TIdent of ident * sort
    | TApply of operation * term list

    member x.getSort() =
        match x with
        | TConst(_, s)
        | TIdent(_, s) ->
            s
        | TApply(op, _) -> op.getSort()

    override x.ToString() =
        match x with
        | TConst(name, _) -> name.ToString()
        | TIdent(name, _) -> name.ToString()
        | TApply(op, []) -> op.ToString()
        | TApply(f, xs) -> sprintf "(%O %s)" f (xs |> List.map toString |> join " ")

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

let notMapApply f z = function
    | Top -> z Bot
    | Bot -> z Top
    | Equal(t1, t2) -> z <| Distinct(t1, t2)
    | Distinct(t1, t2) -> z <| Equal(t1, t2)
    | AApply(op, ts) -> f op ts

let private simplBinary zero one deconstr constr =
    let rec iter k = function
        | [] -> k []
        | x :: xs ->
            if x = one then x
            elif x = zero then iter k xs
            else
                match deconstr x with
                | Some ys -> iter (fun ys -> iter (fun xs -> k (ys @ xs)) xs) ys
                | None -> iter (fun res -> k (x :: res)) xs
    iter (function [] -> zero | [t] -> t | ts -> ts |> constr)

module Terms =
    let mapFold = List.mapFold
    let map = List.map

module Term =
    let typeOf = function
        | TConst(_, typ)
        | TIdent(_, typ)
        | TApply(ElementaryOperation(_, _, typ), _)
        | TApply(UserDefinedOperation(_, _, typ), _) -> typ

    let rec mapFold f z = function
        | TConst(name, typ) ->
            let (name, typ), z = f z (name, typ)
            TConst(name, typ), z
        | TIdent(name, typ) ->
            let (name, typ), z = f z (name, typ)
            TIdent(name, typ), z
        | TApply(op, ts) ->
            let ts, z = Terms.mapFold (mapFold f) z ts
            TApply(op, ts), z

    let rec map f = function
        | TConst(name, typ) ->
            let name, typ = f (name, typ)
            TConst(name, typ)
        | TIdent(name, typ) ->
            let name, typ = f (name, typ)
            TIdent(name, typ)
        | TApply(op, ts) ->
            let ts = Terms.map (map f) ts
            TApply(op, ts)

    let rec bind f = function
        | TIdent(name, typ)
        | TConst(name, typ) as t -> f t (name, typ)
        | TApply(op, ts) ->
            let ts = Terms.map (bind f) ts
            TApply(op, ts)

    let substituteWith substMap = bind (fun t vs -> Option.defaultValue t <| Map.tryFind vs substMap)

    let substituteWithPair v t u =
        let rec substInTermWithPair = function
            | TConst _ as c -> c
            | TIdent(v1, s1) as vs1 -> if v = (v1, s1) then t else vs1
            | TApply(op, ts) -> TApply(op, List.map substInTermWithPair ts)
        substInTermWithPair u

module Atom =
    let mapFold f z = function
        | Top
        | Bot as a -> a, z
        | Equal(t1, t2) ->
            let t1, z = f z t1
            let t2, z = f z t2
            Equal(t1, t2), z
        | Distinct(t1, t2) ->
            let t1, z = f z t1
            let t2, z = f z t2
            Distinct(t1, t2), z
        | AApply(op, ts) ->
            let ts, z = Terms.mapFold f z ts
            AApply(op, ts), z

    let map f = function
        | Top
        | Bot as a -> a
        | Equal(t1, t2) ->
            let t1 = f t1
            let t2 = f t2
            Equal(t1, t2)
        | Distinct(t1, t2) ->
            let t1 = f t1
            let t2 = f t2
            Distinct(t1, t2)
        | AApply(op, ts) ->
            let ts = Terms.map f ts
            AApply(op, ts)

    let substituteWith freshVarsMap = map (Term.substituteWith freshVarsMap)

module Atoms =
    let map = List.map
    let mapFold = List.mapFold

type 'a conjunction = Conjunction of 'a list
type 'a disjunction = Disjunction of 'a list
type dnf = atom conjunction disjunction
type cnf = atom disjunction conjunction

type conditional<'a> = atom list * 'a
module Conditional =
    let toCondition x : 'a conditional = [], x

    let toString ((conds, a) : 'a conditional) =
        let a = a.ToString()
        match conds with
        | [] -> a
        | [c] -> $"(=> %O{c} {a})"
        | _ -> $"""(=> (and {conds |> List.map toString |> join " "}) {a})"""

    let pair ((conds1, x1) : term conditional) ((conds2, x2) : term conditional) : (term * term) conditional = conds1 @ conds2, (x1, x2)
    let list (cnds : 'a conditional list) : ('a list) conditional =
        let cnds, xs = List.unzip cnds
        List.concat cnds, xs
    let mapHead f ((conds, x) : 'a conditional) : 'b conditional = conds, f x
    let strengthen conds1 ((conds2, x) : 'a conditional) : 'a conditional = conds1 @ conds2, x
    let bind f ((conds1, x) : 'a conditional) : 'b conditional =
        let conds2, y = f x
        conds1 @ conds2, y
    let map2 f ((conds1, x) : 'a conditional) ((conds2, y) : 'b conditional) = conds1 @ conds2, f x y
    let toConj ((conds, x) : atom conditional) : atom conjunction = Conjunction <| x :: conds

    let map fConds mapChild ((conds, a) : 'a conditional) : 'b conditional =
        Atoms.map fConds conds, mapChild a

    let mapFold fConds mapFoldChild z ((conds, a) : 'a conditional) : 'a conditional * _ =
        let conds, z = Atoms.mapFold fConds z conds
        let a, z = mapFoldChild z a
        (conds, a), z

    let substituteWith freshVarsMap = map (Atom.substituteWith freshVarsMap)

type quantifier =
    | ForallQuantifier of sorted_var list
    | ExistsQuantifier of sorted_var list
    | StableForallQuantifier of sorted_var list // for metavariables, such as in let bindings

type quantifiers = quantifier list

module Quantifier =
    let negate = function
        | ForallQuantifier vars -> ExistsQuantifier vars
        | ExistsQuantifier vars -> ForallQuantifier vars
        | StableForallQuantifier _ as q -> q

    let unquantify = function
        | ForallQuantifier vars -> ForallQuantifier, vars
        | ExistsQuantifier vars -> ExistsQuantifier, vars
        | StableForallQuantifier vars -> StableForallQuantifier, vars

    let remove toRemove q =
        let qc, vars = unquantify q
        match List.filter (fun v -> not <| Set.contains v toRemove) vars with
        | [] -> None
        | vars -> Some <| qc vars

    let mapFold f z q =
        let qConstr, vars = unquantify q
        let vars, z = f z vars
        qConstr vars, z

    let withFreshVariables = mapFold SortedVars.withFreshVariables

    let toString q =
        let name, vars =
            match q with
            | ForallQuantifier vars -> "forall", vars
            | ExistsQuantifier vars -> "exists", vars
            | StableForallQuantifier vars -> "forall", vars
        fun body -> $"""(%s{name} (%s{vars |> List.map (fun (v, e) -> $"({v} {e})") |> join " "})%s{"\n\t"}%s{body})"""

module Quantifiers =
    let empty : quantifiers = []

    let mapFold f z (qs : quantifiers) = List.mapFold f z qs

    let existsp : (quantifier -> bool) -> quantifiers -> bool = List.exists

    let (|ForallQuantifiersOrEmpty|_|) qs =
        List.foldChoose (fun vars -> function ForallQuantifier vars' | StableForallQuantifier vars' -> Some (vars @ vars') | _ -> None) [] qs

    let add q (qs : quantifiers) : quantifiers =
        match q with
        | ForallQuantifier []
        | ExistsQuantifier []
        | StableForallQuantifier [] -> qs
        | _ ->
        match qs with
        | [] -> [q]
        | q'::qs ->
        match q, q' with
        | ForallQuantifier vars, ForallQuantifier vars' -> ForallQuantifier (vars @ vars')::qs
        | ExistsQuantifier vars, ExistsQuantifier vars' -> ExistsQuantifier (vars @ vars')::qs
        | StableForallQuantifier vars, StableForallQuantifier vars' -> StableForallQuantifier (vars @ vars')::qs
        | _ -> q::q'::qs

    let combine (outer : quantifiers) (inner : quantifiers) : quantifiers =
        match inner with
        | [] -> outer
        | _ ->
            let inner, innerLast = List.butLast inner
            inner @ add innerLast outer

    let combineMany (qss : quantifiers list) : quantifiers =
        match qss with
        | [] -> empty
        | qs::qss -> List.fold combine qs qss

    let forall vars : quantifiers = add (ForallQuantifier vars) empty
    let exists vars : quantifiers = add (ExistsQuantifier vars) empty
    let stableforall vars : quantifiers = add (StableForallQuantifier vars) empty

    let negate (qs : quantifiers) : quantifiers = List.map Quantifier.negate qs

    let withFreshVariables (qs : quantifiers) : quantifiers * Map<_,_> =
        mapFold Quantifier.withFreshVariables Map.empty qs

    let private squashStableIntoForall (qs : quantifiers) =
        List.foldBack add (List.map (function StableForallQuantifier vars -> ForallQuantifier vars | q -> q) qs) empty

    let remove toRemove (qs : quantifiers) =
        List.foldBack (fun q qs -> match Quantifier.remove toRemove q with Some q -> add q qs | None -> qs) qs empty

    let toString (qs : quantifiers) o = List.foldBack Quantifier.toString (squashStableIntoForall qs) (o.ToString())

type rule =
    | Rule of quantifiers * atom list * atom
    | Equivalence of quantifiers * atom list * atom
    override x.ToString() =
        match x with
        | Rule(qs, xs, x) ->
            match xs with
            | [] -> $"{x}"
            | [y] -> $"(=> {y}\n\t    {x})"
            | _ -> sprintf "(=>\t(and %s)\n\t\t%O)" (xs |> List.map toString |> join "\n\t\t\t") x
            |> Quantifiers.toString qs
        | Equivalence(qs, xs, x) ->
            match xs with
            | [] -> $"{x}"
            | [y] -> $"(= {y}\n\t    {x})"
            | _ -> sprintf "(=\t(and %s)\n\t\t%O)" (xs |> List.map toString |> join "\n\t\t\t") x
            |> Quantifiers.toString qs
let private baseRule q fromAtoms toAtom =
    let fromAtoms = List.filter ((<>) Top) fromAtoms
    Rule(q, fromAtoms, toAtom)
let aerule forallVars existsVars fromAtoms toAtom = baseRule (Quantifiers.add (ExistsQuantifier existsVars) <| Quantifiers.forall forallVars) fromAtoms toAtom
let rule vars fromAtoms toAtom = baseRule (Quantifiers.forall vars) fromAtoms toAtom
let eqRule vars fromAtoms toAtom = Equivalence((Quantifiers.forall vars), fromAtoms, toAtom)

type definition =
    | DefineFun of function_def
    | DefineFunRec of function_def
    | DefineFunsRec of function_def list
    override x.ToString() =
        match x with
        | DefineFunRec(name, vars, returnType, body) ->
            $"(define-fun-rec {Symbols.sprintForDeclare name} (%s{SortedVars.toString vars}) {returnType} {body})"
        | DefineFun(name, vars, returnType, body) ->
            $"(define-fun {Symbols.sprintForDeclare name} (%s{SortedVars.toString vars}) {returnType} {body})"
        | DefineFunsRec fs ->
            let signs, bodies = List.map (fun (n, vs, s, b) -> (n, vs, s), b) fs |> List.unzip
            let signs = signs |> List.map (fun (name, vars, sort) -> $"(%s{Symbols.sprintForDeclare name} (%s{SortedVars.toString vars}) {sort})") |> join " "
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
            List.map (fun (c, args) -> $"({c} %s{SortedVars.toString args})") >> join " " >> sprintf "(%s)"
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
let private lemmaToString pred vars lemma =
    $"""(lemma {pred} ({vars |> List.map (fun (v, s) -> $"(%O{v} %O{s})") |> join " "}) %O{lemma})"""
type originalCommand =
    | Definition of definition
    | Command of command
    | Assert of smtExpr
    | Lemma of symbol * sorted_var list * smtExpr
    override x.ToString() =
        match x with
        | Definition df -> df.ToString()
        | Command cmnd -> cmnd.ToString()
        | Assert f -> $"(assert {f})"
        | Lemma(pred, vars, lemma) -> lemmaToString pred vars lemma

type folFormula =
    | FOLAtom of atom
    | FOLNot of folFormula
    | FOLOr of folFormula list
    | FOLAnd of folFormula list
    override x.ToString() =
        match x with
        | FOLAtom a -> a.ToString()
        | FOLNot a -> $"(not %O{a})"
        | FOLOr ats -> $"""(or {ats |> List.map toString |> join " "})"""
        | FOLAnd ats -> $"""(and {ats |> List.map toString |> join " "})"""
let rec folNot = function
    | FOLNot f -> f
    | FOLAtom a -> notMapApply (fun op ts -> AApply(op, ts) |> FOLAtom |> FOLNot) FOLAtom a
    | f -> FOLNot f
let folOr = simplBinary (FOLAtom Bot) (FOLAtom Top) (function FOLOr xs -> Some xs | _ -> None) FOLOr
let folAnd = simplBinary (FOLAtom Top) (FOLAtom Bot) (function FOLAnd xs -> Some xs | _ -> None) FOLAnd

module FOL =
    let map f =
        let rec iter = function
            | FOLAtom a -> FOLAtom (f a)
            | FOLNot f -> f |> iter |> FOLNot
            | FOLAnd fs -> fs |> List.map iter |> FOLAnd
            | FOLOr fs -> fs |> List.map iter |> FOLOr
        iter

    let bind f =
        let rec iter = function
            | FOLAtom a -> f a
            | FOLNot f -> f |> iter |> FOLNot
            | FOLAnd fs -> fs |> List.map iter |> folAnd
            | FOLOr fs -> fs |> List.map iter |> folOr
        iter

    let mapFold f z =
        let rec iter z = function
            | FOLAtom a ->
                let a', z' = f z a
                FOLAtom a', z'
            | FOLNot f ->
                let f', z' = iter z f
                FOLNot f', z'
            | FOLAnd fs ->
                let fs', z' = List.mapFold iter z fs
                FOLAnd fs', z'
            | FOLOr fs ->
                let fs', z' = List.mapFold iter z fs
                FOLOr fs', z'
        iter z

    let mapFoldPositivity f pos z =
        let rec iter pos z = function
            | FOLAtom a ->
                let a', z' = f pos z a
                a', z'
            | FOLNot f ->
                let f', z' = iter (not pos) z f
                FOLNot f', z'
            | FOLAnd fs ->
                let fs', z' = List.mapFold (iter pos) z fs
                FOLAnd fs', z'
            | FOLOr fs ->
                let fs', z' = List.mapFold (iter pos) z fs
                FOLOr fs', z'
        iter pos z

    let substituteWith freshVarsMap = map (Atom.substituteWith freshVarsMap)

type lemma = quantifiers * folFormula conditional

module Lemma =
    let withFreshVariables ((qs, cond) : lemma) =
        let qs, freshVarsMap = Quantifiers.withFreshVariables qs
        let freshVarsMap = Map.map (fun _ -> TIdent) freshVarsMap
        let cond = Conditional.substituteWith freshVarsMap (FOL.substituteWith freshVarsMap) cond
        qs, cond

    let toString ((qs, cond) : lemma) =
        Conditional.toString cond |> Quantifiers.toString qs

let private simplQuant constr zero one e = function
    | [] -> e
    | vars -> if e = zero then zero elif e = one then one else constr(vars, e)
let truee = BoolConst true
let falsee = BoolConst false
let ore = simplBinary falsee truee (function Or xs -> Some xs | _ -> None) Or
let ande = simplBinary truee falsee (function And xs -> Some xs | _ -> None) And
let forall vars e = simplQuant Forall falsee truee e vars
let exists vars e = simplQuant Exists falsee truee e vars
//let folForall, folExists =
//    let zero = FOLBase (FOLAtom Bot)
//    let one = FOLBase (FOLAtom Top)
//    let folForall vars body = simplQuant FOLForall zero one body vars
//    let folExists vars body = simplQuant FOLExists zero one body vars
//    folForall, folExists
type transformedCommand =
    | OriginalCommand of command
    | TransformedCommand of rule
    | LemmaCommand of symbol * sorted_var list * lemma * lemma // body lemma, head cube
    override x.ToString() =
        match x with
        | OriginalCommand x -> x.ToString()
        | TransformedCommand x -> $"(assert %O{x})"
        | LemmaCommand(pred, vars, bodyLemma, headCube) ->
            lemmaToString pred vars (join " " [Lemma.toString bodyLemma; Lemma.toString headCube])
type folCommand =
    | FOLOriginalCommand of command
    | FOLAssertion of quantifiers * folFormula
    override x.ToString() =
        match x with
        | FOLOriginalCommand x -> x.ToString()
        | FOLAssertion(qs, x) -> $"(assert %s{Quantifiers.toString qs x})"
let truet = TConst("true", boolSort)
let falset = TConst("false", boolSort)
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
let folAssert (qs, e) =
    match e with
    | FOLAtom Top -> None
    | _ -> Some (FOLAssertion(qs, e))
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

module Conj =
    let singleton x = Conjunction [x]
    let exponent (Conjunction cs : 'a disjunction conjunction) : 'a conjunction disjunction =
        List.map (function Disjunction cs -> cs) cs |> List.product |> List.map Conjunction |> Disjunction
    let map produce_disjunction (Conjunction dss) =
        List.map (produce_disjunction >> Disjunction) dss |> Conjunction
    let bind (produce_disjunction : atom -> atom list) =
        map (function Disjunction ds -> List.collect produce_disjunction ds)
    let flatten (Conjunction css : 'a conjunction conjunction) = List.collect (function Conjunction cs -> cs) css |> Conjunction
    let toFOL (Conjunction cs : atom conjunction) = cs |> List.map FOLAtom |> folAnd

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
    let toFOL (Disjunction cs : dnf) = cs |> List.map Conj.toFOL |> folOr

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
