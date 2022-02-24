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
//    let gensym = function
//        | PrimitiveSort s -> IdentGenerator.gensymp s |> PrimitiveSort
//        | _ -> __unreachable__()
//
    let sortToFlatString s =
        let rec sortToFlatString = function
            | BoolSort -> ["Bool"]
            | IntSort -> ["Int"]
            | FreeSort s
            | ADTSort s -> [s]
            | ArraySort(s1, s2) -> "Array" :: sortToFlatString s1 @ sortToFlatString s2
        sortToFlatString s |> join ""

    let compare (s1 : sort) (s2 : sort) =
        let s1 = sortToFlatString s1
        let s2 = sortToFlatString s2
        s1.CompareTo(s2)

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

    let changeName name = function
        | ElementaryOperation(_, s1, s2) -> ElementaryOperation(name, s1, s2)
        | UserDefinedOperation(_, s1, s2) -> UserDefinedOperation(name, s1, s2)

    let flipOperationKind = function
        | UserDefinedOperation(n, s1, s2) -> ElementaryOperation(n, s1, s2)
        | ElementaryOperation(n, s1, s2) -> UserDefinedOperation(n, s1, s2)

    let makeUserOperationFromVars name vars retSort = UserDefinedOperation(name, List.map snd vars, retSort)
    let makeUserOperationFromSorts name argSorts retSort = UserDefinedOperation(name, argSorts, retSort)
    let makeUserRelationFromVars name vars = makeUserOperationFromVars name vars BoolSort
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

module Term =
    let truth = TConst("true", BoolSort)
    let falsehood = TConst("false", BoolSort)

    let fromBool b = if b then truth else falsehood

    let apply op xs = TApply(op, xs)
    let apply0 op = apply op []
    let apply1 op t = apply op [t]
    let apply2 op x y = apply op [x; y]
    let apply3 op x y z = apply op [x; y; z]

    let generateVariable sort = TIdent(IdentGenerator.gensym (), sort)
    let generateVariableWithPrefix name sort = TIdent(IdentGenerator.gensymp name, sort)

    let typeOf = function
        | TConst(_, typ)
        | TIdent(_, typ) -> typ
        | TApply(op, _) -> Operation.returnType op

    let rec mapFold f z = function
        | TConst(name, typ) ->
            let (name, typ), z = f z (name, typ)
            TConst(name, typ), z
        | TIdent(name, typ) ->
            let (name, typ), z = f z (name, typ)
            TIdent(name, typ), z
        | TApply(op, ts) ->
            let ts, z = List.mapFold (mapFold f) z ts
            TApply(op, ts), z

    let rec map f = function
        | TConst(name, typ) ->
            let name, typ = f (name, typ)
            TConst(name, typ)
        | TIdent(name, typ) ->
            let name, typ = f (name, typ)
            TIdent(name, typ)
        | TApply(op, ts) ->
            let ts = List.map (map f) ts
            TApply(op, ts)

    let rec bind f = function
        | TIdent(name, typ)
        | TConst(name, typ) as t -> f t (name, typ)
        | TApply(op, ts) ->
            let ts = List.map (bind f) ts
            TApply(op, ts)

    let substituteWith substMap = bind (fun t vs -> Option.defaultValue t <| Map.tryFind vs substMap)

    let substituteWithPair v t u =
        let rec substInTermWithPair = function
            | TConst _ as c -> c
            | TIdent(v1, s1) as vs1 -> if v = (v1, s1) then t else vs1
            | TApply(op, ts) -> TApply(op, List.map substInTermWithPair ts)
        substInTermWithPair u

    let collectFreeVars =
        let rec iter = function
            | TIdent(i, s) -> [i, s]
            | TConst _ -> []
            | TApply(_, ts) -> List.collect iter ts
        iter >> List.unique

module Terms =
    let mapFold = List.mapFold
    let map = List.map

    let collectFreeVars = List.collect Term.collectFreeVars >> List.unique

    let generateVariablesFromVars vars = List.map ((<||) Term.generateVariableWithPrefix) vars
    let generateVariablesFromOperation = Operation.argumentTypes >> List.map Term.generateVariable

    let generateNVariablesOfSort n sort = List.init n (fun _ -> Term.generateVariable sort)

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

module Atom =
    let apply op xs = AApply(op, xs)
    let apply1 op x = apply op [x]
    let apply2 op x y = apply op [x; y]

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

    let collectFreeVars = function
       | AApply(_, ts) -> Terms.collectFreeVars ts
       | Equal(t1, t2) | Distinct(t1, t2) -> Terms.collectFreeVars [t1; t2]
       | Bot | Top -> []

module Atoms =
    let map = List.map
    let mapFold = List.mapFold

    let collectFreeVars = List.collect Atom.collectFreeVars >> List.unique

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

    let getVars = function
        | ForallQuantifier vars
        | ExistsQuantifier vars
        | StableForallQuantifier vars -> vars

    let private unquantify = function
        | ForallQuantifier vars -> ForallQuantifier, vars
        | ExistsQuantifier vars -> ExistsQuantifier, vars
        | StableForallQuantifier vars -> StableForallQuantifier, vars

    let remove toRemove q =
        let qc, vars = unquantify q
        match List.filter (fun v -> not <| Set.contains v toRemove) vars with
        | [] -> None
        | vars -> Some <| qc vars

    let map f q =
        let qConstr, vars = unquantify q
        let vars = f vars
        qConstr vars
    
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

    let getVars = List.collect Quantifier.getVars
    
    let map f (qs : quantifiers) = List.map f qs
    
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

    let simplify constr zero one e = function
        | [] -> e
        | vars -> if e = zero then zero elif e = one then one else constr(vars, e)

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

module Rule =
    let private baseRule q fromAtoms toAtom =
        Rule(q, fromAtoms, toAtom)

    let aerule forallVars existsVars fromAtoms toAtom =
        let forallVars = Terms.collectFreeVars forallVars
        let existsVars = Terms.collectFreeVars existsVars
        baseRule (Quantifiers.combine (Quantifiers.forall forallVars) (Quantifiers.exists existsVars)) fromAtoms toAtom

    let private arule vars fromAtoms toAtom = baseRule (Quantifiers.forall vars) fromAtoms toAtom

    let clARule fromAtoms toAtom =
        let freeVars = Atoms.collectFreeVars (toAtom :: fromAtoms)
        arule freeVars fromAtoms toAtom

    let clAFact toAtom = clARule [] toAtom

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
    | FOLEq of folFormula * folFormula
    override x.ToString() =
        match x with
        | FOLAtom a -> a.ToString()
        | FOLNot a -> $"(not {a})"
        | FOLOr ats -> $"""(or {ats |> List.map toString |> join " "})"""
        | FOLAnd ats -> $"""(and {ats |> List.map toString |> join " "})"""
        | FOLEq(a, b) -> $"(= {a} {b})"

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

module FOL =
    let rec folNot = function
        | FOLNot f -> f
        | FOLAtom a -> notMapApply (fun op ts -> AApply(op, ts) |> FOLAtom |> FOLNot) FOLAtom a
        | f -> FOLNot f
    let folOr = simplBinary (FOLAtom Bot) (FOLAtom Top) (function FOLOr xs -> Some xs | _ -> None) FOLOr
    let folAnd = simplBinary (FOLAtom Top) (FOLAtom Bot) (function FOLAnd xs -> Some xs | _ -> None) FOLAnd

    let hence a b = folOr [folNot a; b]

    let map f =
        let rec iter = function
            | FOLAtom a -> FOLAtom (f a)
            | FOLNot f -> f |> iter |> FOLNot
            | FOLAnd fs -> fs |> List.map iter |> FOLAnd
            | FOLOr fs -> fs |> List.map iter |> FOLOr
            | FOLEq(a, b) -> FOLEq(iter a, iter b)
        iter

    let bind f =
        let rec iter = function
            | FOLAtom a -> f a
            | FOLNot f -> f |> iter |> FOLNot
            | FOLAnd fs -> fs |> List.map iter |> folAnd
            | FOLOr fs -> fs |> List.map iter |> folOr
            | FOLEq(a, b) -> FOLEq(iter a, iter b)
        iter

    let fold f z =
        let rec iter z = function
            | FOLAtom a -> f z a
            | FOLNot f -> iter z f
            | FOLAnd fs
            | FOLOr fs -> List.fold iter z fs
            | FOLEq(a, b) ->
                let z' = iter z a
                iter z' b
        iter z

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
            | FOLEq(a, b) ->
                let a', z' = iter z a
                let b', z'' = iter z' b
                FOLEq(a', b'), z''
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
            | FOLEq(a, b) ->
                let a', z' = iter pos z a
                let b', z'' = iter pos z' b
                FOLEq(a', b'), z''
        iter pos z

    let private collectFreeVarsWith free fol = fold (fun free atom -> Atom.collectFreeVars atom |> Set.ofList |> Set.union free) free fol
    let collectFreeVars fol = collectFreeVarsWith Set.empty fol |> Set.toList
    let collectFreeVarsOfList fols = List.fold collectFreeVarsWith Set.empty fols |> Set.toList

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

module FOLCommand =
    let private aequivalence vars fromAtom toAtom = FOLAssertion(Quantifiers.forall vars, FOLEq(fromAtom, toAtom))
    let private arule vars body head = FOLAssertion(Quantifiers.forall vars, FOL.hence body head)
    let private afact vars head = FOLAssertion(Quantifiers.forall vars, FOLAtom head)

    let clAEquivalence body head =
       let freeVars = Atoms.collectFreeVars (head :: body)
       aequivalence freeVars (FOL.folAnd <| List.map FOLAtom body) (FOLAtom head)

    let clARule body head =
        let freeVars = Atoms.collectFreeVars (head :: body)
        arule freeVars (FOL.folAnd <| List.map FOLAtom body) (FOLAtom head)

    let clAFact head =
        let freeVars = Atom.collectFreeVars head
        afact freeVars head

let folAssert (qs, e) =
    match e with
    | FOLAtom Top -> None
    | _ -> Some (FOLAssertion(qs, e))

module Conj =
    let singleton x = Conjunction [x]
    let exponent (Conjunction cs : 'a disjunction conjunction) : 'a conjunction disjunction =
        List.map (function Disjunction cs -> cs) cs |> List.product |> List.map Conjunction |> Disjunction
    let map produce_disjunction (Conjunction dss) =
        List.map (produce_disjunction >> Disjunction) dss |> Conjunction
    let bind (produce_disjunction : atom -> atom list) =
        map (function Disjunction ds -> List.collect produce_disjunction ds)
    let flatten (Conjunction css : 'a conjunction conjunction) = List.collect (function Conjunction cs -> cs) css |> Conjunction
    let toFOL (Conjunction cs : atom conjunction) = cs |> List.map FOLAtom |> FOL.folAnd

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
    let toFOL (Disjunction cs : dnf) = cs |> List.map Conj.toFOL |> FOL.folOr

[<Struct>]
type CollectBuilder =
    member __.Bind(xs, binder) = List.collect binder xs
    member __.Bind(Disjunction dss : dnf, binder) = List.collect (function Conjunction cs -> binder cs) dss
    member __.Return(value) = [value]
    member __.ReturnFrom(value) = value
let collector = CollectBuilder()
