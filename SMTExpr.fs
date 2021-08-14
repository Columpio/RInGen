module RInGen.SMTExpr
open Antlr4.Runtime
open Antlr4.Runtime.Tree
open RInGen.Operations
open Antlr4.Runtime
open SMTLIB2Parser

let private parseSymbol (e : SMTLIBv2Parser.SymbolContext) : string =
    match e.GetChild(0) with
    | :? SMTLIBv2Parser.SimpleSymbolContext as s ->
        match s.GetChild(0) with
        | :? SMTLIBv2Parser.PredefSymbolContext as s -> s.GetChild(0).GetText()
        | _ -> s.UndefinedSymbol().ToString()
    | :? SMTLIBv2Parser.QuotedSymbolContext as s -> s.GetChild(0).GetText()
    | _ -> __unreachable__()

let private parseSymbolAsSort (e : SMTLIBv2Parser.SymbolContext) = parseSymbol e |> PrimitiveSort

let private parseNumeral (e : SMTLIBv2Parser.NumeralContext) : int64 = int64 <| e.Numeral().ToString()

let private parseIndex (e : SMTLIBv2Parser.IndexContext) =
    match e.GetChild(0) with
    | :? SMTLIBv2Parser.SymbolContext as s -> parseSymbol s
    | :? SMTLIBv2Parser.NumeralContext as n -> parseNumeral n |> toString
    | _ -> __unreachable__()

let private parseIdentifier (e : SMTLIBv2Parser.IdentifierContext) =
    let s = e.symbol() |> parseSymbol
    if e.ChildCount = 1 then s else
    let indices = e.index() |> List.ofArray |> List.map parseIndex
    s //TODO: indices are ignored

let rec private parseSort (expr : SMTLIBv2Parser.SortContext) =
    let ident = expr.identifier() |> parseIdentifier
    let sorts = expr.sort() |> List.ofArray
    match sorts with
    | [] -> PrimitiveSort ident
    | _ -> CompoundSort(ident, List.map parseSort sorts)

let private parseQualifiedIdentifier (expr : SMTLIBv2Parser.Qual_identifierContext) =
    let ident = expr.identifier() |> parseIdentifier
    if expr.ChildCount = 1
        then ident
        else __notImplemented__()

let private parseSortedVar (expr : SMTLIBv2Parser.Sorted_varContext) =
    let v = expr.symbol() |> parseSymbol
    let s = expr.sort() |> parseSort
    v, s

let private parseSymbolAndNumeralAsSort s n =
    let name = parseSymbol s
    let n = parseNumeral n
    match n with
    | 0L -> PrimitiveSort name
    | _ -> failwithf $"Generic sorts are not supported: %s{name} %d{n}"

let private parseSortDec (expr : SMTLIBv2Parser.Sort_decContext) =
    parseSymbolAndNumeralAsSort (expr.symbol()) (expr.numeral())

let private parseSelector (e : SMTLIBv2Parser.Selector_decContext) =
    let sel = e.symbol() |> parseSymbol
    let sort = e.sort() |> parseSort
    sel, sort

let private parseConstant (e : SMTLIBv2Parser.Spec_constantContext) =
    match e.GetChild(0) with
    | :? SMTLIBv2Parser.NumeralContext as n -> Number <| parseNumeral n
    | :? SMTLIBv2Parser.DecimalContext
    | :? SMTLIBv2Parser.HexadecimalContext
    | :? SMTLIBv2Parser.BinaryContext
    | :? SMTLIBv2Parser.StringContext -> __notImplemented__()
    | _ -> __unreachable__()

let private parseDatatypeDeclaration typer adtname (dec : SMTLIBv2Parser.Datatype_decContext) =
    let handle_constr typer (constr : SMTLIBv2Parser.Constructor_decContext) =
        let fname = parseSymbol <| constr.symbol()
        let selectors = constr.selector_dec() |> List.ofArray |> List.map parseSelector
        let _, typer = Typer.addADTOperations typer adtname fname selectors
        (fname, selectors), typer
    let constrs = dec.constructor_dec() |> List.ofArray
    match constrs with
    | [] -> __notImplemented__()
    | _ -> List.mapFold handle_constr typer constrs

let rec private parseVarBinding te (expr : SMTLIBv2Parser.Var_bindingContext) =
    let v = expr.symbol() |> parseSymbol
    let e = expr.term() |> parseTerm te
    let s = Typer.typeOf e
    let vs = (v, s)
    let te = VarEnv.replaceOne te vs
    (vs, e), te

and private parseTerm ((typer : Typer.Typer, env) as te) (e : SMTLIBv2Parser.TermContext) =
    match e.GetChild(0) with
    | :? SMTLIBv2Parser.Spec_constantContext as c -> parseConstant c
    | :? SMTLIBv2Parser.Qual_identifierContext as ident ->
        match parseQualifiedIdentifier ident with
        | "true" -> BoolConst true
        | "false" -> BoolConst false
        | ident ->
            match typer.tryFind ident with
            | Some c -> Apply(c, [])
            | None -> Ident(ident, VarEnv.typeGet ident te)
    | _ ->
        match e.GetChild(1) with
        | :? SMTLIBv2Parser.Qual_identifierContext as op ->
            let op = parseQualifiedIdentifier op
            let args = e.term() |> List.ofArray |> List.map (parseTerm te)
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
                let oper = Typer.fillOperation typer (symbol op) (List.map Typer.typeOf args)
                match op, args with
                | "+", [Apply(ElementaryOperation("-", _, _) as minusOp, [t1]); t2] -> Apply(minusOp, [t2; t1]) // TODO: #parseWorkaround (+ (- a) b) = (- b a)
                | "<=", [t1; Apply(ElementaryOperation("-", _, _), [t2])] ->
                    Apply(oper, [Apply(DummyOperations.addOp, [t1; t2]); Number 0L])// (<= a (- b)) = (<= (+ a b) 0)
                | _ when typer.containsKey op -> Apply(oper, args)
                | _ -> __notImplemented__()
        | :? ITerminalNode as node ->
            match node.GetText() with
            | "forall" ->
                let vars = e.sorted_var() |> List.ofArray |> List.map parseSortedVar
                let te = VarEnv.replace te vars
                let body = e.term(0) |> parseTerm te
                Forall(vars, body)
            | "exists" ->
                let vars = e.sorted_var() |> List.ofArray |> List.map parseSortedVar
                let te = VarEnv.replace te vars
                let body = e.term(0) |> parseTerm te
                Exists(vars, body)
            | "let" ->
                let bindings, te = e.var_binding() |> List.ofArray |> List.mapFold parseVarBinding te
                let body = e.term(0) |> parseTerm te
                Let(bindings, body)
            | "match" ->
                let t = e.term(0) |> parseTerm te
                let typ = Typer.typeOf t
                let extendEnvironment ((typer, env) as te) ((v, typ) as vt) =
                    match Typer.tryTypeCheck v typer with
                    | Some _ -> Ident vt, te
                    | None ->
                        let te = VarEnv.replaceOne te vt
                        Ident vt, te
                let handle_case (e : SMTLIBv2Parser.Match_caseContext) =
                    let pat = e.pattern().symbol() |> List.ofArray |> List.map parseSymbol
                    let body = e.term()
                    match pat with
                    | constr::cargs ->
                        match Typer.tryGetOperation typer constr with
                        | Some op -> // constructor pattern
                            let cargs, te = List.mapFold extendEnvironment te (List.zip cargs (Operation.argumentTypes op))
                            Apply(op, cargs), parseTerm te body
                        | None -> //variable
                            assert (List.isEmpty cargs)
                            let v, te = extendEnvironment te (constr, typ)
                            v, parseTerm te body
                    | [] -> __unreachable__()
                let cases = e.match_case() |> List.ofArray |> List.map handle_case
                Match(t, cases)
            | _ -> __notImplemented__()
        | _ -> __unreachable__()

let private parseFunctionDeclaration (e : SMTLIBv2Parser.Function_decContext) =
    let name = e.symbol() |> parseSymbol
    let vars = e.sorted_var() |> List.ofArray |> List.map parseSortedVar
    let retSort = e.sort() |> parseSort
    name, vars, retSort

let parseFunctionDefinition typer (e : SMTLIBv2Parser.Function_defContext) defineFunTermConstr =
    let name = e.symbol() |> parseSymbol
    let vars = e.sorted_var() |> List.ofArray |> List.map parseSortedVar
    let sort = e.sort() |> parseSort
    let typer = Typer.addOperation name (Operation.makeUserOperationFromVars name vars sort) typer
    let te = VarEnv.create typer vars
    let body = e.term() |> parseTerm te
    Definition(defineFunTermConstr(name, vars, sort, body)), typer

let private parseAttribute (attr : SMTLIBv2Parser.AttributeContext) =
    let keyword = attr.keyword().GetText()
    let value = if attr.ChildCount = 1 then None else Some <| attr.attribute_value().GetText()
    keyword, value

let private parseToTerms commands =
    let toComm typer (e : SMTLIBv2Parser.CommandContext) =
        let comm, typer =
            match e.GetChild(1) with
            | :? SMTLIBv2Parser.Cmd_exitContext -> Command Exit, typer
            | :? SMTLIBv2Parser.Cmd_defineFunContext -> parseFunctionDefinition typer (e.function_def()) DefineFun
            | :? SMTLIBv2Parser.Cmd_defineFunRecContext -> parseFunctionDefinition typer (e.function_def()) DefineFunRec
            | :? SMTLIBv2Parser.Cmd_defineFunsRecContext  ->
                let signs = e.function_dec() |> List.ofArray |> List.map parseFunctionDeclaration
                let bodies = e.term() |> List.ofArray
                let typer = List.fold (fun typer (name, vars, sort) -> Typer.addOperation name (Operation.makeUserOperationFromVars name vars sort) typer) typer signs
                let fs = List.map2 (fun body (name, vars, sort) -> name, vars, sort, parseTerm (VarEnv.create typer vars) body) bodies signs
                Definition <| DefineFunsRec fs, typer
            | :? SMTLIBv2Parser.Cmd_declareDatatypeContext ->
                let adtname = e.symbol(0) |> parseSymbolAsSort
                let constrs, typer = e.datatype_dec(0) |> parseDatatypeDeclaration typer adtname
                Command(DeclareDatatype(adtname, constrs)), typer
            | :? SMTLIBv2Parser.Cmd_declareDatatypesContext ->
                let signs = e.sort_dec() |> List.ofArray
                let constr_groups = e.datatype_dec() |> List.ofArray
                let names = List.map parseSortDec signs
                let dfs, typer = List.mapFold (fun typer (name, constrs) -> parseDatatypeDeclaration typer name constrs) typer (List.zip names constr_groups)
                Command(DeclareDatatypes (List.zip names dfs)), typer
            | :? SMTLIBv2Parser.Cmd_checkSatContext -> Command CheckSat, typer
            | :? SMTLIBv2Parser.Cmd_getModelContext -> Command GetModel, typer
            | :? SMTLIBv2Parser.Cmd_getProofContext -> Command GetProof, typer
            | :? SMTLIBv2Parser.Cmd_setOptionContext -> Command (SetOption(e.option().children |> Seq.map (fun t -> t.GetText()) |> join " ")), typer
            | :? SMTLIBv2Parser.Cmd_getInfoContext -> Command (GetInfo(e.info_flag().GetText())), typer
            | :? SMTLIBv2Parser.Cmd_setInfoContext -> Command (SetInfo(parseAttribute <| e.attribute())), typer
            | :? SMTLIBv2Parser.Cmd_assertContext ->
                let expr = e.GetChild<SMTLIBv2Parser.TermContext>(0)
                Assert(parseTerm (typer, VarEnv.empty) expr), typer
            | :? SMTLIBv2Parser.Cmd_declareSortContext ->
                let sort = parseSymbolAndNumeralAsSort (e.symbol(0)) (e.numeral())
                DeclareSort(sort) |> Command, typer
            | :? SMTLIBv2Parser.Cmd_declareConstContext ->
                let name = e.symbol(0) |> parseSymbol
                let sort = e.sort(0) |> parseSort
                DeclareConst(name, sort) |> Command, Typer.addOperation name (Operation.makeUserOperationFromSorts name [] sort) typer
            | :? SMTLIBv2Parser.Cmd_declareFunContext ->
                let name = e.GetChild<SMTLIBv2Parser.SymbolContext>(0) |> parseSymbol
                let argTypes, sort = e.sort() |> List.ofArray |> List.map parseSort |> List.butLast
                DeclareFun(name, argTypes, sort) |> Command, Typer.addOperation name (Operation.makeUserOperationFromSorts name argTypes sort) typer
            | :? SMTLIBv2Parser.Cmd_setLogicContext->
                let name = e.GetChild<SMTLIBv2Parser.SymbolContext>(0)
                SetLogic(parseSymbol name) |> Command, typer
            | e -> failwithf $"{e}"
        comm, typer
    let commands = List.ofArray commands
    let comms, _ = List.mapFold toComm Typer.empty commands
    comms

let parseFile filename =
    let file = AntlrFileStream(filename)
    let lexer = SMTLIBv2Lexer(file)
    let tokenStream = CommonTokenStream(lexer)
    let parser = SMTLIBv2Parser(tokenStream)
    let commands = parser.start().script().command()
    let commands = parseToTerms commands
    commands