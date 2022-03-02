[<AutoOpen>]
module RInGen.Prelude

type symbol = string
type ident = string

module Symbols =
    let addPrefix (pref : string) s = pref + s

type sort =
    | BoolSort
    | IntSort
    | FreeSort of ident
    | ADTSort of ident
    | ArraySort of sort * sort
    override x.ToString() =
        match x with
        | BoolSort -> "Bool"
        | IntSort -> "Int"
        | FreeSort s
        | ADTSort s -> s
        | ArraySort(s1, s2) -> $"(Array {s1} {s2})"

module Sort =
    let sortToFlatString s =
        let rec sortToFlatString = function
            | BoolSort -> ["Bool"]
            | IntSort -> ["Int"]
            | FreeSort s
            | ADTSort s -> [s]
            | ArraySort(s1, s2) -> "Array" :: sortToFlatString s1 @ sortToFlatString s2
        sortToFlatString s |> join ""

    let compare (s1 : sort) (s2 : sort) =
        let s1 = hash s1
        let s2 = hash s2
        s1.CompareTo(s2)

type sorted_var = symbol * sort

module SortedVar =
    let freshFromSort s : sorted_var = IdentGenerator.gensym (), s
    let freshFromVar ((v, s) : sorted_var) : sorted_var = IdentGenerator.gensymp v, s

    let compare ((v1, s1) : sorted_var) ((v2, s2) : sorted_var) =
        let cmpSorts = Sort.compare s1 s2
        // prioritize sort name in comparison
        if cmpSorts = 0 then v1.CompareTo(v2) else cmpSorts

module SortedVars =
    let mapFold = List.mapFold

    let sort = List.sortWith SortedVar.compare

    let withFreshVariables = List.mapFold (fun freshVarsMap vs -> let vs' = SortedVar.freshFromVar vs in vs', Map.add vs vs' freshVarsMap)

    let generateNVariablesOfSort n sort = List.init n (fun _ -> SortedVar.freshFromSort sort)

    let toString : sorted_var list -> string = List.map (fun (v, s) -> $"({v} {s})") >> join " "

type operation =
    | ElementaryOperation of ident * sort list * sort
    | UserDefinedOperation of ident * sort list * sort

    override x.ToString() =
        match x with
        | ElementaryOperation(s, _, _)
        | UserDefinedOperation(s, _, _) -> toString s

module Operation =
    let argumentTypes = function
        | ElementaryOperation(_, s, _)
        | UserDefinedOperation(_, s, _) -> s
    let returnType = function
        | ElementaryOperation(_, _, s)
        | UserDefinedOperation(_, _, s) -> s
    let opName = function
        | ElementaryOperation(n, _, _)
        | UserDefinedOperation(n, _, _) -> n
    let toTuple = function
        | ElementaryOperation(n, a, s)
        | UserDefinedOperation(n, a, s) -> n, a, s

    let isUserOperation = function UserDefinedOperation _ -> true | _ -> false

    let changeName name = function
        | ElementaryOperation(_, s1, s2) -> ElementaryOperation(name, s1, s2)
        | UserDefinedOperation(_, s1, s2) -> UserDefinedOperation(name, s1, s2)

    let flipOperationKind = function
        | UserDefinedOperation(n, s1, s2) -> ElementaryOperation(n, s1, s2)
        | ElementaryOperation(n, s1, s2) -> UserDefinedOperation(n, s1, s2)

    let makeUserOperationFromVars name vars retSort = UserDefinedOperation(name, List.map snd vars, retSort)
    let makeUserOperationFromSorts name argSorts retSort = UserDefinedOperation(name, argSorts, retSort)
    let makeUserRelationFromVars name vars = makeUserOperationFromVars name vars BoolSort
    let makeUserRelationFromSorts name sorts = makeUserOperationFromSorts name sorts BoolSort
    let makeElementaryOperationFromVars name vars retSort = ElementaryOperation(name, List.map snd vars, retSort)
    let makeElementaryOperationFromSorts name argSorts retSort = ElementaryOperation(name, argSorts, retSort)
    let makeElementaryRelationFromVars name vars = makeElementaryOperationFromVars name vars BoolSort
    let makeElementaryRelationFromSorts name argSorts = makeElementaryOperationFromSorts name argSorts BoolSort

    let makeADTOperations adtSort cName tName selectorSorts =
        let cOp = makeElementaryOperationFromVars cName selectorSorts adtSort
        let tOp = makeElementaryOperationFromSorts tName [adtSort] BoolSort
        let selOps = List.map (fun (selName, selSort) -> makeElementaryOperationFromSorts selName [adtSort] selSort) selectorSorts
        cOp, tOp, selOps

//
//    let private operationToIdent = function
//        | UserDefinedOperation(name, [], ret) -> Ident(name, ret)
//        | ElementaryOperation(name, [], ret) -> Ident(name, ret)
//        | op -> failwithf $"Can't create identifier from operation: {op}"

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

type quantifier =
    | ForallQuantifier of sorted_var list
    | ExistsQuantifier of sorted_var list
    | StableForallQuantifier of sorted_var list // for metavariables, such as in let bindings

module Quantifier =
    let toString q =
        let name, vars =
            match q with
            | ForallQuantifier vars -> "forall", vars
            | ExistsQuantifier vars -> "exists", vars
            | StableForallQuantifier vars -> "forall", vars
        fun body -> $"""(%s{name} (%s{vars |> List.map (fun (v, e) -> $"({v} {e})") |> join " "})%s{"\n\t"}%s{body})"""

type quantifiers = quantifier list

module Quantifiers =
    let empty : quantifiers = []

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

    let private squashStableIntoForall (qs : quantifiers) =
        List.foldBack add (List.map (function StableForallQuantifier vars -> ForallQuantifier vars | q -> q) qs) empty

    let toString (qs : quantifiers) o = List.foldBack Quantifier.toString (squashStableIntoForall qs) (o.ToString())

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
    | QuantifierApplication of quantifiers * smtExpr
    override x.ToString() =
        let term_list_to_string = List.map toString >> join " "
        let atom_list_to_string = List.map toString >> join " "
        let bindings_to_string = List.map (fun ((v, _), e) -> $"({v} {e})") >> join " "
        match x with
        | Apply(f, []) -> f.ToString()
        | Apply(f, xs) -> $"({f} {term_list_to_string xs})"
        | Number n -> toString n
        | BoolConst true -> "true"
        | BoolConst false -> "false"
        | Ident(x, _) -> x.ToString()
        | Let(bindings, body) ->
            $"(let (%s{bindings_to_string bindings}) {body})"
        | Match(t, cases) ->
            sprintf "(match %O (%s))" t (cases |> List.map (fun (pat, t) -> $"({pat} {t})") |> join " ")
        | Ite(i, t, e) -> $"(ite {i} {t} {e})"
        | And xs -> $"(and {atom_list_to_string xs})"
        | Or xs -> $"(or {atom_list_to_string xs})"
        | Not x -> $"(not {x})"
        | Hence(i, t) -> $"(=> {i} {t})"
        | QuantifierApplication(qs, e) -> Quantifiers.toString qs e

let QuantifierApplication(qs, body) =
    match qs with
    | [] -> body
    | _ -> QuantifierApplication(qs, body)

type function_def = symbol * sorted_var list * sort * smtExpr

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

type definition =
    | DefineFun of function_def
    | DefineFunRec of function_def
    | DefineFunsRec of function_def list
    override x.ToString() =
        match x with
        | DefineFunRec(name, vars, returnType, body) ->
            $"(define-fun-rec {name} (%s{SortedVars.toString vars}) {returnType} {body})"
        | DefineFun(name, vars, returnType, body) ->
            $"(define-fun {name} (%s{SortedVars.toString vars}) {returnType} {body})"
        | DefineFunsRec fs ->
            let signs, bodies = List.map (fun (n, vs, s, b) -> (n, vs, s), b) fs |> List.unzip
            let signs = signs |> List.map (fun (name, vars, sort) -> $"({name} ({SortedVars.toString vars}) {sort})") |> join " "
            let bodies = bodies |> List.map toString |> join " "
            $"(define-funs-rec (%s{signs}) (%s{bodies}))"

type datatype_def = symbol * (operation * operation * operation list) list // adt name, [constr, tester, [selector]]

module Datatype =
    let noConstructorArity = 0

    let maxConstructorArity ((_, cs) : datatype_def) = cs |> List.map (thd3 >> List.length) |> List.max

type command =
    | CheckSat
    | GetModel
    | Exit
    | GetInfo of string
    | GetProof
    | SetInfo of string * string option
    | SetLogic of string
    | SetOption of string
    | DeclareDatatype of datatype_def
    | DeclareDatatypes of datatype_def list
    | DeclareFun of symbol * sort list * sort
    | DeclareSort of symbol
    | DeclareConst of symbol * sort
    override x.ToString() =
        let constrEntryToString (constrOp, _, selOps) =
            $"""({Operation.opName constrOp} {Operation.argumentTypes constrOp |> List.zip selOps |> List.map (fun (selOp, argSort) -> $"({Operation.opName selOp} {argSort})") |> join " "})"""
        let constrsOfOneADTToString = List.map constrEntryToString >> join " " >> sprintf "(%s)"
        let dtsToString dts =
            let sortNames, ops = List.unzip dts
            let sorts = sortNames |> List.map (sprintf "(%O 0)") |> join " "
            let constrs = ops |> List.map constrsOfOneADTToString |> join " "
            $"""(declare-datatypes ({sorts}) ({constrs}))"""
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
        | DeclareFun(name, args, ret) -> $"""(declare-fun {name} ({args |> List.map toString |> join " "}) {ret})"""
        | DeclareDatatype dt -> dtsToString [dt]
        | DeclareDatatypes dts -> dtsToString dts

let private oldDtToNewDt oldDt = // TODO: delete this with refactoring
    let adtSort, fs = oldDt
    let adtSortName =
        match adtSort with
        | ADTSort adtSortName -> adtSortName
        | _ -> __notImplemented__()
    let toADTOps (cName, selectorSorts) =
        let tName = "is-" + cName
        Operation.makeADTOperations adtSort cName tName selectorSorts
    adtSortName, List.map toADTOps fs

let DeclareDatatype oldDt =
    DeclareDatatype(oldDtToNewDt oldDt)

let DeclareDatatypes oldDts =
    DeclareDatatypes(List.map oldDtToNewDt oldDts)

module Command =
    let declareOp = function
        | ElementaryOperation(name, argSorts, retSort)
        | UserDefinedOperation(name, argSorts, retSort) -> DeclareFun(name, argSorts, retSort)

    let maxConstructorArity = function
        | DeclareDatatype dt -> Datatype.maxConstructorArity dt
        | DeclareDatatypes dts -> dts |> List.map Datatype.maxConstructorArity |> List.max
        | _ -> Datatype.noConstructorArity

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

    let toStringCommand pred vars lemma =
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
        | Lemma(pred, vars, lemma) -> Lemma.toStringCommand pred vars lemma

let notMapApply f z = function
    | Bot -> z Top
    | Top -> z Bot
    | Equal(t1, t2) -> z <| Distinct(t1, t2)
    | Distinct(t1, t2) -> z <| Equal(t1, t2)
    | AApply(op, ts) -> f op ts

let simplBinary zero one deconstr constr =
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
