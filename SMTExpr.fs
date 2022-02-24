module RInGen.SMTExpr
open System.Collections.Generic
open Antlr4.Runtime
open Antlr4.Runtime.Misc
open Antlr4.Runtime.Tree
open Context
open RInGen
open SMTLIB2Parser

let truth = BoolConst true
let falsehood = BoolConst false

let ore = simplBinary falsehood truth (function Or xs -> Some xs | _ -> None) Or
let ande = simplBinary truth falsehood (function And xs -> Some xs | _ -> None) And

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
    | QuantifierApplication(qs, body) -> QuantifierApplication(Quantifiers.negate qs, note body)
    | e -> Not e

and private simplee = function
    | Not (Not e) -> simplee e
    | Not e -> note e
    | And e -> ande e
    | Or e -> ore e
    | e -> e

let rec private typeOf = function
    | Not _
    | Hence _
    | And _
    | Or _
    | QuantifierApplication _
    | BoolConst _ -> BoolSort
    | Number _ -> IntSort
    | Ident(_, t) -> t
    | Apply(op, _) -> Operation.returnType op
    | Match(_, (_, t)::_)
    | Ite(_, t, _)
    | Let(_, t) -> typeOf t
    | Match(_, []) -> __unreachable__()

//    let forall vars e = Quantifiers.simplify Forall falsehood truth e vars
//    let exists vars e = Quantifiers.simplify Exists falsehood truth e vars

let private makePrimitiveTerm = function
    | Choice1Of2 op -> Apply(op, []) // user-defined constant
    | Choice2Of2(ident, sort) -> Ident(ident, sort)

type private env = Map<ident, sorted_var>

module private Env =
    let empty : env = Map.empty

    let ofList vars : env = vars |> List.map (fun ((v, _) as vs) -> v, vs) |> Map.ofList

    let replaceOne (env : env) (var, sort) : sorted_var * env =
        let var' = IdentGenerator.gensymp var, sort
        var', Map.add var var' env

type VarEnvSaver (env : VarEnv) =
    member x.Delay f =
        env.SaveState ()
        let r = f ()
        env.LoadState ()
        r
    member x.Return o = o

and VarEnv(ctx : Context, vars2sorts) as this =
    let state = Stack<_>()
    let saver = VarEnvSaver(this)
    new (ctx : Context) = VarEnv(ctx, Dictionary<ident, sort>())

    member x.WithVars vars = x.Add vars; x

    member x.ctx = ctx

    abstract member SaveState : unit -> unit
    default x.SaveState () = state.Push(Dictionary.copy vars2sorts)

    abstract member LoadState : unit -> unit
    default x.LoadState () =
        let n' = state.Pop()
        vars2sorts.Clear()
        Dictionary.copyContents vars2sorts n'

    member x.InIsolation () = saver

    abstract member TryFindDefinedOperation : ident -> operation option
    default x.TryFindDefinedOperation ident = ctx.TryFindDefinedOperation ident

    member private x.TryGetFromIdent var =
        match Dictionary.tryGetValue var vars2sorts with
        | Some sort -> Some(var, sort)
        | None -> None

    member x.TryGetSorted (i : ident) =
        match ctx.TryFindDefinedOperation i with
        | Some c -> Some (Choice1Of2 c)
        | None ->
            match x.TryGetFromIdent i with
            | Some sv -> Some (Choice2Of2 sv)
            | None -> None

    member x.GetSorted (i : ident) =
        match x.TryGetSorted i with
        | Some v -> v
        | None -> failwith $"Identifier is not found in the environment: {i}"

    member x.AddOne var sort = vars2sorts.Add(var, sort)

    member x.Add vars = List.iter vars2sorts.Add vars

    abstract member ReplaceOneVarOrConstructor : ident * sort -> Choice<operation, ident * sort>
    default x.ReplaceOneVarOrConstructor(ident, sort) =
        match x.TryGetSorted ident with
        | Some(Choice1Of2 _ as op) -> op
        | Some(Choice2Of2 _)
        | None ->
            x.AddOne ident sort
            Choice2Of2(ident, sort)

    member x.ReplaceVarOrConstructor args = List.map x.ReplaceOneVarOrConstructor args

    member x.FillOperation opName argTypes = ctx.FillOperation opName argTypes

type private SubstVarEnv(ctx : Context, osyms2nsyms, nvars2nsorts) as this =
    inherit VarEnv(ctx, nvars2nsorts)

    let state = Stack<_>()
    let saver = VarEnvSaver(this)
    new (ctx : Context) = SubstVarEnv(ctx, Dictionary<ident, ident>(), Dictionary<ident, sort>())

    override x.SaveState () =
        base.SaveState ()
        state.Push(Dictionary.copy osyms2nsyms)

    override x.LoadState () =
        base.LoadState ()
        let o' = state.Pop()
        osyms2nsyms.Clear()
        Dictionary.copyContents osyms2nsyms o'

    member x.InIsolation () = saver

    member private x.TryFindSymbol symbol =
        if ctx.IsPredefinedSymbol symbol then Some symbol else Dictionary.tryGetValue symbol osyms2nsyms

    member x.FindSymbol symbol =
        match x.TryFindSymbol symbol with
        | Some symbol -> symbol
        | None -> failwith $"{symbol} is not found in the environment"

    member x.AddSymbol symbol =
        let symbol' = IdentGenerator.gensymp symbol
        osyms2nsyms.Add(symbol, symbol')
        symbol'

    member private x.FindOrAddSymbol symbol =
        match x.TryFindSymbol symbol with
        | Some symbol -> symbol
        | None -> x.AddSymbol symbol

    override x.ReplaceOneVarOrConstructor(ident, sort) =
        let ident = x.FindOrAddSymbol ident
        base.ReplaceOneVarOrConstructor(ident, sort)

    override x.TryFindDefinedOperation ident =
        match x.TryFindSymbol ident with
        | Some ident -> base.TryFindDefinedOperation ident
        | None -> None

    member x.GetSorted (i : ident) =
        opt {
            let! i' = x.TryFindSymbol i
            let! c = x.TryGetSorted i'
            return c
        } |> Option.defaultWith (fun () -> failwith $"Identifier is not found in the environment: {i}")

let private parseNumeral (e : SMTLIBv2Parser.NumeralContext) : int64 = int64 <| e.Numeral().ToString()

let private parseConstant (e : SMTLIBv2Parser.Spec_constantContext) =
    match e.GetChild(0) with
    | :? SMTLIBv2Parser.NumeralContext as n -> Number <| parseNumeral n
    | :? SMTLIBv2Parser.DecimalContext
    | :? SMTLIBv2Parser.HexadecimalContext
    | :? SMTLIBv2Parser.BinaryContext
    | :? SMTLIBv2Parser.StringContext -> __notImplemented__()
    | _ -> __unreachable__()

let private parseAttribute (attr : SMTLIBv2Parser.AttributeContext) =
    let keyword = attr.keyword().GetText()
    let value = if attr.ChildCount = 1 then None else Some <| attr.attribute_value().GetText()
    keyword, value

type private InteractiveReader () =
    inherit BaseInputCharStream()

    let data = List<char>()
    override x.ValueAt(i) = int data.[i];
    override x.ConvertDataToString(start, count) = new string(data.ToArray(), start, count)

    member x.Add(line) =
        data.AddRange(line)
        x.n <- data.Count
    member x.ResetPointer () = x.p <- 0
    member x.SetStart(i) =
        data.RemoveRange(0, i)
        x.n <- data.Count
        x.p <- 0

type private ThrowingErrorListener () =
    inherit BaseErrorListener()

    static member INSTANCE = ThrowingErrorListener()

    override x.SyntaxError(output, recognizer, offendingSymbol, line, charPositionInLine, msg, e) = raise e

type private symbolVersion = Raw | Old | New

and Parser () as this =
    inherit Context()
    let interactiveReader = InteractiveReader ()
    let lexer = SMTLIBv2Lexer(interactiveReader)
    let parser = SMTLIBv2Parser(CommonTokenStream(lexer))
    let mutable env = SubstVarEnv(this)
    do
        parser.ErrorHandler <- BailErrorStrategy()
        parser.RemoveErrorListeners()
        parser.AddErrorListener(ThrowingErrorListener.INSTANCE)

    member private x.ParseSymbol version (e : SMTLIBv2Parser.SymbolContext) : string =
        let symbol =
            match e.GetChild(0) with
            | :? SMTLIBv2Parser.SimpleSymbolContext as s ->
                match s.GetChild(0) with
                | :? SMTLIBv2Parser.PredefSymbolContext as s -> s.GetChild(0).GetText()
                | _ -> s.UndefinedSymbol().ToString()
            | :? SMTLIBv2Parser.QuotedSymbolContext as s -> s.GetChild(0).GetText()
            | _ -> __unreachable__()
        match version with
        | Raw -> symbol
        | Old -> env.FindSymbol symbol
        | New -> env.AddSymbol symbol

    member private x.ParseIndex version (e : SMTLIBv2Parser.IndexContext) =
        match e.GetChild(0) with
        | :? SMTLIBv2Parser.SymbolContext as s -> x.ParseSymbol version s
        | :? SMTLIBv2Parser.NumeralContext as n -> parseNumeral n |> toString
        | _ -> __unreachable__()

    member private x.ParseIdentifier version (e : SMTLIBv2Parser.IdentifierContext) =
        let s = e.symbol() |> x.ParseSymbol version
        if e.ChildCount = 1 then s else
//        let indices = e.index() |> List.ofArray |> List.map x.ParseIndex
        s //TODO: indices are ignored

    member private x.ParseQualifiedIdentifier (expr : SMTLIBv2Parser.Qual_identifierContext) =
        let ident = expr.identifier() |> x.ParseIdentifier Raw
        if expr.ChildCount = 1
            then ident
            else __notImplemented__()

    member private x.ParseSort version (expr : SMTLIBv2Parser.SortContext) =
        let ident = expr.identifier() |> x.ParseIdentifier version
        let argSorts = expr.sort() |> List.ofArray |> List.map (x.ParseSort version)
        x.FindSort ident argSorts

    member private x.ParseSymbolAndNumeralAsSort s n =
        let name = x.ParseSymbol New s
        let n = parseNumeral n
        match n with
        | 0L -> name
        | _ -> failwith $"Generic sorts are not supported: {name} {n}"

    member private x.ParseSortedVars exprs =
        let parseSortedVar (expr : SMTLIBv2Parser.Sorted_varContext) =
            let v = expr.symbol() |> x.ParseSymbol New
            let s = expr.sort() |> x.ParseSort Old
            v, s
        exprs |> List.ofArray |> List.map parseSortedVar

    member private x.ParseSortDec (expr : SMTLIBv2Parser.Sort_decContext) =
        x.ParseSymbolAndNumeralAsSort (expr.symbol()) (expr.numeral())

    member private x.ParseSelector (e : SMTLIBv2Parser.Selector_decContext) =
        let sel = e.symbol() |> x.ParseSymbol New
        let sort = e.sort() |> x.ParseSort Old
        sel, sort

    member private x.ParseVarBinding (expr : SMTLIBv2Parser.Var_bindingContext) =
        let v = expr.symbol() |> x.ParseSymbol New
        let e = expr.term() |> x.ParseTerm
        let s = typeOf e
        env.AddOne v s
        ((v, s), e)

    member private x.ParseTerm (e : SMTLIBv2Parser.TermContext) =
        match e.GetChild(0) with
        | :? SMTLIBv2Parser.Spec_constantContext as c -> parseConstant c
        | :? SMTLIBv2Parser.Qual_identifierContext as ident ->
            match x.ParseQualifiedIdentifier ident with
            | "true" -> truth
            | "false" -> falsehood
            | ident -> ident |> env.GetSorted |> makePrimitiveTerm
        | _ ->
            match e.GetChild(1) with
            | :? SMTLIBv2Parser.Qual_identifierContext as op ->
                let op = x.ParseQualifiedIdentifier op
                let args = e.term() |> List.ofArray |> List.map x.ParseTerm
                match () with
                | _ when List.contains op ["and"; "or"; "not"; "=>"; "ite"] ->
                    match op, args with
                    | "and", _ -> ande args
                    | "or", _ -> ore args
                    | "not", [arg] -> Not arg
                    | "=>", [i; t] -> Hence(i, t)
                    | "ite", [i; t; e] -> Ite(i, t, e)
                    | e -> failwithf $"{e}"
                | _ ->
                    let op = env.FindSymbol op
                    let oper = env.FillOperation op (List.map typeOf args)
                    Apply(oper, args)
            | :? ITerminalNode as node ->
                match node.GetText() with
                | "let" ->
                    env.InIsolation () {
                        let bindings = e.var_binding() |> List.ofArray |> List.map x.ParseVarBinding
                        let body = e.term(0) |> x.ParseTerm
                        return Let(bindings, body)
                    }
                | "match" ->
                    let t = e.term(0) |> x.ParseTerm
                    let typ = typeOf t
                    let extendEnvironment args = // vars are old, sorts are new
                        let args = env.ReplaceVarOrConstructor args
                        List.map makePrimitiveTerm args
                    let extendEnvironmentOne v typ = // v is old, typ is new
                        let vt = env.ReplaceOneVarOrConstructor(v, typ)
                        makePrimitiveTerm vt
                    let handle_case (e : SMTLIBv2Parser.Match_caseContext) =
                        env.InIsolation () {
                            let pat = e.pattern().symbol() |> List.ofArray |> List.map (x.ParseSymbol Raw)
                            let body = e.term()
                            match pat with
                            | constr::cargs ->
                                return opt {
                                    let! op = env.TryFindDefinedOperation constr
                                    let cargs = extendEnvironment (List.zip cargs (Operation.argumentTypes op))
                                    return Apply(op, cargs), x.ParseTerm body
                                } |> Option.defaultWith (fun () -> // variable
                                    assert (List.isEmpty cargs)
                                    let v = extendEnvironmentOne constr typ
                                    v, x.ParseTerm body)
                            | [] -> return __unreachable__()
                        }
                    let cases = e.match_case() |> List.ofArray |> List.map handle_case
                    Match(t, cases)
                | quantifierName ->
                    let q =
                        match quantifierName with
                        | "forall" -> Some Quantifiers.forall
                        | "exists" -> Some Quantifiers.exists
                        | _ -> None
                    env.InIsolation () {
                        return opt {
                            let! q = q
                            let vars = e.sorted_var() |> x.ParseSortedVars
                            let q = q vars
                            env.Add vars
                            let body = e.term(0) |> x.ParseTerm
                            match body with
                            | QuantifierApplication(qs, body) -> return QuantifierApplication(Quantifiers.combine q qs, body)
                            | _ -> return QuantifierApplication(q, body)
                        } |> Option.defaultWith __notImplemented__
                    }
            | _ -> __unreachable__()

    member private x.ParseDatatypeDeclaration adtname (dec : SMTLIBv2Parser.Datatype_decContext) =
        let parseConstr (constr : SMTLIBv2Parser.Constructor_decContext) =
            let fname = x.ParseSymbol New <| constr.symbol()
            let selectors = constr.selector_dec() |> List.ofArray |> List.map x.ParseSelector
            fname, selectors
        let constrs = dec.constructor_dec() |> List.ofArray
        x.AddRawADTSort adtname
        let constrs = List.map parseConstr constrs
        x.AddRawADTOperations adtname constrs

    member private x.ParseFunctionDefinition (e : SMTLIBv2Parser.Function_defContext) defineFunTermConstr =
        let name = e.symbol() |> x.ParseSymbol New
        env.InIsolation () {
            let vars = e.sorted_var() |> x.ParseSortedVars
            let sort = e.sort() |> x.ParseSort Old
            x.AddOperation name (Operation.makeUserOperationFromVars name vars sort)
            env.Add vars
            let body = x.ParseTerm (e.term())
            return Definition(defineFunTermConstr(name, vars, sort, body))
        }

    member private x.ParseFunctionDeclaration (e : SMTLIBv2Parser.Function_decContext) =
        e.symbol() |> x.ParseSymbol New, e.sorted_var(), x.ParseSort Old (e.sort())

    member private x.ParseCommand (e : SMTLIBv2Parser.CommandContext) =
        match e.GetChild(1) with
        | :? SMTLIBv2Parser.Cmd_exitContext -> Command Exit
        | :? SMTLIBv2Parser.Cmd_defineFunContext -> x.ParseFunctionDefinition (e.function_def()) DefineFun
        | :? SMTLIBv2Parser.Cmd_defineFunRecContext -> x.ParseFunctionDefinition (e.function_def()) DefineFunRec
        | :? SMTLIBv2Parser.Cmd_defineFunsRecContext ->
            let handleFunction (name, ovars, retSort) body =
                env.InIsolation () {
                    let vars = ovars |> x.ParseSortedVars
                    x.AddOperation name (Operation.makeUserOperationFromVars name vars retSort)
                    env.Add vars
                    return name, vars, retSort, x.ParseTerm body
                }
            let signs = e.function_dec() |> List.ofArray |> List.map x.ParseFunctionDeclaration
            let bodies = e.term() |> List.ofArray
            let fs = List.map2 handleFunction signs bodies
            Definition <| DefineFunsRec fs
        | :? SMTLIBv2Parser.Cmd_declareDatatypeContext ->
            let adtname = e.symbol(0) |> x.ParseSymbol New
            let constrs = e.datatype_dec(0) |> x.ParseDatatypeDeclaration adtname
            Command(command.DeclareDatatype(adtname, constrs))
        | :? SMTLIBv2Parser.Cmd_declareDatatypesContext ->
            let signs = e.sort_dec() |> List.ofArray
            let constr_groups = e.datatype_dec() |> List.ofArray
            let names = List.map x.ParseSortDec signs
            let dfs = List.map2 x.ParseDatatypeDeclaration names constr_groups
            Command(command.DeclareDatatypes(List.zip names dfs))
        | :? SMTLIBv2Parser.Cmd_checkSatContext -> Command CheckSat
        | :? SMTLIBv2Parser.Cmd_getModelContext -> Command GetModel
        | :? SMTLIBv2Parser.Cmd_getProofContext -> Command GetProof
        | :? SMTLIBv2Parser.Cmd_setOptionContext -> Command (SetOption(e.option().children |> Seq.map (fun t -> t.GetText()) |> join " "))
        | :? SMTLIBv2Parser.Cmd_getInfoContext -> Command (GetInfo(e.info_flag().GetText()))
        | :? SMTLIBv2Parser.Cmd_setInfoContext -> Command (SetInfo(parseAttribute <| e.attribute()))
        | :? SMTLIBv2Parser.Cmd_lemmaContext ->
            let predName = e.symbol(0) |> x.ParseSymbol Old
            env.InIsolation () {
                let vars = e.sorted_var() |> x.ParseSortedVars
                let lemma = x.ParseTerm (e.term(0))
                return Lemma(predName, vars, lemma)
            }
        | :? SMTLIBv2Parser.Cmd_assertContext ->
            let expr = e.GetChild<SMTLIBv2Parser.TermContext>(0)
            env.InIsolation () { return Assert(x.ParseTerm expr) }
        | :? SMTLIBv2Parser.Cmd_declareSortContext ->
            let sort = x.ParseSymbolAndNumeralAsSort (e.symbol(0)) (e.numeral())
            DeclareSort(sort) |> Command
        | :? SMTLIBv2Parser.Cmd_declareConstContext ->
            let name = e.symbol(0) |> x.ParseSymbol New
            let sort = e.sort(0) |> x.ParseSort Old
            x.AddOperation name (Operation.makeUserOperationFromSorts name [] sort)
            DeclareConst(name, sort) |> Command
        | :? SMTLIBv2Parser.Cmd_declareFunContext ->
            let name = e.GetChild<SMTLIBv2Parser.SymbolContext>(0) |> x.ParseSymbol New
            let argTypes, sort = e.sort() |> List.ofArray |> List.map (x.ParseSort Old) |> List.butLast
            x.AddOperation name (Operation.makeUserOperationFromSorts name argTypes sort)
            DeclareFun(name, argTypes, sort) |> Command
        | :? SMTLIBv2Parser.Cmd_setLogicContext->
            let name = e.GetChild<SMTLIBv2Parser.SymbolContext>(0)
            SetLogic(x.ParseSymbol Raw name) |> Command
        | e -> failwithf $"{e}"

    member private x.ParseCommands = List.ofArray >> List.map x.ParseCommand

    member x.ParseFile filename =
        let file = AntlrFileStream(filename)
        lexer.SetInputStream(file)
        let commands = parser.start().script().command()
        let commands = x.ParseCommands commands
        commands

    member x.ParseLine (line : string) =
        interactiveReader.Add(line)
        lexer.SetInputStream(interactiveReader)
        parser.TokenStream <- CommonTokenStream(lexer)
        let commands = List<_>()
        try
            while interactiveReader.Size > 0 do
                let command = parser.command()
                commands.Add(x.ParseCommand command)
                let lastParsedIndex = 1 + command.Stop.StopIndex
                interactiveReader.SetStart(lastParsedIndex)
        with :? ParseCanceledException | :? NoViableAltException -> interactiveReader.ResetPointer()
        List.ofSeq commands
