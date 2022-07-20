module RInGen.Synchronization
open System.Collections.Generic
open SMTLIB2
open SMTLIB2.IdentGenerator

type private POB = term list list

let private combineNames ns = join "" ns |> gensymp

let private topFreeVarsOf (pob : POB) = List.collect (List.choose (function TIdent(v, s) -> Some(v, s) | _ -> None)) pob |> List.unique

let private uniformizeVars pob =
    let u = Term.Uniformizer()
    List.map (List.map u.Uniformize) pob

let rec private product (xss : 'a list list) : 'a list seq =
    match xss with
    | [] -> seq [[]]
    | xs::xss -> seq { for x in xs do for ys in product xss do yield x::ys }

let rec private synchronizeArguments argss = // Hardcoded synchronization strategy!
    let takeHeadsAndTails xss = List.choose (function [] -> None | x::xs -> Some(x, xs)) xss |> List.unzip
    let hs, ts = takeHeadsAndTails argss
    match hs, ts with
    | [], [] -> []
    | _ -> hs :: synchronizeArguments ts

let private synchronizeConstructorCalls ccs = // Hardcoded synchronization strategy!
    let combConstrName, argss = List.unzip ccs // [Cons; Nil; Cons], [Nil; Nil; Nil]
    let combArgs = synchronizeArguments argss // [[#4; #4]; [Nil; Nil]]
    combConstrName, combArgs

type private POBDB (adts) =
    let pobs = Dictionary()
    let rules = Dictionary()
    let adt_declarations = Dictionary()
    let comb_sorts = Dictionary()
    let comb_constructors = Dictionary()
    do for s, ops in adts do
        adt_declarations.Add(s, ops)
        comb_sorts.Add([s], s)
        for op in ops do
            comb_constructors.Add([op], op)

    member private x.RegisterCombinedSort sorts comb_sort =
        if comb_sorts.ContainsKey(sorts) then () else
        comb_sorts.Add(sorts, comb_sort)
        let ccs = List.map (fun sort -> adt_declarations.[sort]) sorts |> product |> List.ofSeq
        let getCombinedConstructor cs =
            let csWithSorts = cs |> List.map (fun c -> c, Operation.argumentTypes c)
            let constr_name, arguments = synchronizeConstructorCalls csWithSorts
            let comb_arguments = List.map x.CombSort arguments
            let comb_constr = x.CombConstrName constr_name comb_arguments
            comb_constr
        let constrOps = List.map getCombinedConstructor ccs
        adt_declarations.Add(comb_sort, constrOps)

    member private x.CombSort sorts =
        match Dictionary.tryFind sorts comb_sorts with
        | Some comb_sort -> comb_sort
        | None ->
        let new_sort = sorts |> List.map (function ADTSort i -> i | _ -> __notImplemented__()) |> combineNames |> ADTSort
        x.RegisterCombinedSort sorts new_sort
        new_sort

    member private x.CombConstrName constrNames argSorts =
        Dictionary.getOrInitWith constrNames comb_constructors (fun () ->
        match Dictionary.tryFind constrNames comb_constructors with
        | Some combinedName -> combinedName
        | None ->
        let names = List.map Operation.opName constrNames
        let retSorts = List.map Operation.returnType constrNames
        let combinedName = combineNames names
        let combinedReturnSort = x.CombSort retSorts
        Operation.makeElementaryOperationFromSorts combinedName argSorts combinedReturnSort)

    member private x.CombVar sorts =
        let sort = x.CombSort sorts
        Term.generateVariable sort

    member private x.RegisterPOB(pob) : operation =
        let pident = IdentGenerator.gensymp "phi"
        let sorts = List.map x.TypeOfCombinedTerm pob
        let op = Operation.makeElementaryRelationFromSorts pident sorts
        pobs.Add(pob, op)
        print_extra_verbose $"""registered {op}: {pob |> List.map (List.map toString >> join ", " >> sprintf "(%s)") |> join "; "}"""
        op

    member private x.TryGetPOB(pob) : operation option = Dictionary.tryFind pob pobs

    member private x.AddCombRule pred rule =
        let predRules = Dictionary.getOrInitWith pred rules (fun () -> [])
        rules.[pred] <- rule::predRules

    member private x.PossibleTerms sorts =
        let instantiateConstructorSignature constrOp =
            let vars = constrOp |> Operation.argumentTypes |> List.map Term.generateVariable
            TApply(constrOp, vars)
        let possibleTermsOfSort sort =
            let constrsSigns = adt_declarations.[sort]
            let possibleTerms = constrsSigns |> List.map instantiateConstructorSignature
            possibleTerms
        let possibleTermsOfEach = sorts |> List.map possibleTermsOfSort
        product possibleTermsOfEach

    member private x.TypeOfCombinedTerm ts = List.map Term.typeOf ts |> x.CombSort

    member private x.CombConstr(constrNames, args) =
        let argSorts = List.map Term.typeOf args
        let op = x.CombConstrName constrNames argSorts
        TApply(op, args)

    member x.CutHeadConstructors pob = // (#1), (#1, #2)
        // (Cons #1 #2, Cons #3 #4), (Cons #1 #4, Nil)
        // phi(v13, v24, v1, v4) = [[#1; #3]; [#2; #4]; [#1]; [#4]], (ConsCons v13 v24, ConsNil v1 v4)
        let rec cutHeadsFromTermTuple = function
            | TConst(name, sort) -> Some(Operation.makeElementaryOperationFromSorts name [] sort, [])
            | TApply(name, args) -> Some(name, args)
            | _ -> None
        let handleTermTuple ts =
            match List.mapChoose cutHeadsFromTermTuple ts with
            | None -> // (Nil, #5, S #6)
                let v = Term.generateVariable (x.TypeOfCombinedTerm ts)
                [ts], [v], v
            | Some constrNamesAndArgs ->
                let combConstrName, combArgs = synchronizeConstructorCalls constrNamesAndArgs
                let argumentPob, argumentVars, predicateHeadArguments = x.CutHeadConstructors combArgs
                argumentPob, argumentVars, x.CombConstr(combConstrName, predicateHeadArguments)
        let argumentPobs, argumentVars, predicateHeadArguments = List.map handleTermTuple pob |> List.unzip3
        List.concat argumentPobs, List.concat argumentVars, predicateHeadArguments

    member private x.InstantiateAndSyncConstructors pob =
        // arg: (Cons #0 #1, #2, Cons #0 #3), (#1, #2, #3)
        // ret: [( [([(#0, #0)], v0)], [ConsNilCons v0 NilNil; NilNilNil]  ); ...]
        let topFreeVars = topFreeVarsOf pob // [#1; #2; #3]
        let topFreeSorts = List.map snd topFreeVars
        seq {
            for possibleTerms in x.PossibleTerms topFreeSorts do
            // seq[[Nil, Nil, Nil]; ...; [Cons(#n, #n+1), Cons(#n+2, #n+3), Cons(#n+4, #n+5]]
                let substVarsMap = List.zip topFreeVars possibleTerms |> Map.ofList
                let rawSubstPob = List.map (List.map (Term.substituteWith substVarsMap)) pob // (Cons #4 Nil, Nil, Cons #4 Nil), (Nil, Nil, Nil)
                let argumentPob, argumentVars, predicateHeadArguments = x.CutHeadConstructors rawSubstPob
                yield argumentPob, argumentVars, predicateHeadArguments
        }

    member x.DumpRules () =
        // close rules with forall
        // generate declarations
        // return
        let ops, rules = rules |> Dictionary.toList |> List.unzip
        let rules = rules |> List.map List.rev |> List.concat |> List.map ((<||) Rule.clARule)
        let decls = List.map Command.declareOp ops
        List.map OriginalCommand decls @ List.map TransformedCommand rules

    member x.DumpADTRules () =
        let constrSignFromOperation op =
            Operation.opName op, List.map (fun s -> gensymp "sel", s) <| Operation.argumentTypes op
        // do sth with selectors
        // order datatypes by types
        // return decls
        let adt_decls = adt_declarations |> Dictionary.toList |> List.map (fun (k, v) -> k, List.map constrSignFromOperation v)
        [DeclareDatatypes adt_decls] //TODO: too lazy, need to order datatypes by dependency

    member x.UnarifyDeclarations commands =
        let unarifyDeclaration = function
            | DeclareFun(name, argSorts, retSort) -> DeclareFun(name, [x.CombSort argSorts], retSort)
            | c -> c
        // map declare-fun sorts with sorts map
        List.map unarifyDeclaration commands

    member private x.SplitIndependentInPob argumentPobAndVars =
        let argPobAndVarsAndFreeVars = List.mapi (fun i (pob, _) -> i, Terms.collectFreeVars pob |> Set.ofList) argumentPobAndVars
        let rec splitIntoClasses freeVars pvs done_pvss rest =
            let rec iter fvs pvs done_pvss queue = function
                | [] ->
                    if Set.count fvs = Set.count freeVars // free vars didn't change
                    then splitEntry (pvs :: done_pvss) queue
                    else splitIntoClasses fvs pvs done_pvss queue
                | (nxtPV, nxtFV)::rest ->
                    if Set.intersect freeVars nxtFV |> Set.isEmpty then
                        iter freeVars pvs done_pvss ((nxtPV, nxtFV)::queue) rest
                    else iter (Set.union freeVars nxtFV) (nxtPV::pvs) done_pvss queue rest
            iter freeVars pvs done_pvss [] rest
        and splitEntry done_pvss = function
            | [] -> done_pvss
            | (pv, freeVars)::rest -> splitIntoClasses freeVars [pv] done_pvss rest
        let splitedPobsAndArgs = splitEntry [] argPobAndVarsAndFreeVars
        let splitedPobsAndArgs = List.map List.sort splitedPobsAndArgs
        let argumentPobAndVars = Array.ofList argumentPobAndVars
        let splitedPobsAndArgs = List.map (List.map (fun i -> Array.item i argumentPobAndVars)) splitedPobsAndArgs
        List.map List.unzip splitedPobsAndArgs

    member x.AnswerMarkedPOB pobWithVars =
        let pobsAndVars = x.SplitIndependentInPob pobWithVars
        List.map (fun (argPob, argVars) -> AApply(x.AnswerPOB argPob, argVars)) pobsAndVars

    member x.AnswerPOB (pob : POB) : operation =
        let pob = uniformizeVars pob
        match x.TryGetPOB pob with
        | Some pred -> pred
        | None ->
        let pobPredicate = x.RegisterPOB(pob)
        let handleInstPob (argumentPob, argumentVars, predicateHeadArguments) =
            let body = x.AnswerMarkedPOB(List.zip argumentPob argumentVars)
            let head = AApply(pobPredicate, predicateHeadArguments)
            x.AddCombRule pobPredicate (body, head)
        let instPobs = x.InstantiateAndSyncConstructors pob
        Seq.iter handleInstPob instPobs
        pobPredicate

    member private x.EquationsToPob vars eqs : (term list * term) list option =
        // for `vars` mapping x |-> (v, [..,x,..]) unify all `eqs` and make one single POB with `v` variables near each query tuple
        let substVar unifier v = Option.defaultValue (TIdent v) <| Map.tryFind v unifier
        let componentVars = vars |> List.collect fst |> Set.ofList
        opt {
            let! unifier = Unifier.fromList componentVars Set.empty (fun _ -> true) eqs |> snd
            let pob = vars |> List.map (fun (vars, v) -> List.map (substVar unifier) vars, v)
            return pob
        }

    member private x.UnarifyOperation = function
        | ElementaryOperation(name, args, ret) -> ElementaryOperation(name, [x.CombSort args], ret)
        | UserDefinedOperation(name, args, ret) -> UserDefinedOperation(name, [x.CombSort args], ret)

    member private x.MakeVarsForArgumentTerms ts =
        let makeVarForArgument t sort =
            let vs = SortedVar.freshFromSort sort
            vs, (t, TIdent vs)

        let argSorts = List.map Term.typeOf ts
        let newVars, eqs = List.map2 makeVarForArgument ts argSorts |> List.unzip
        let vars = List.choose (function TIdent(v, s) -> Some(v, s) | _ -> None) ts
//        if List.length vars = List.length ts // all terms are variables
//            then vars, [], argSorts
//            else
        newVars, eqs, argSorts

    member private x.UnarifyAtom (vars : ((ident * sort) list * term) list) : atom -> ((term * term) list * atom option) * ((ident * sort) list * term) list = function
        | AApply(op, ts) ->
            let op = x.UnarifyOperation op
            let new_vars, eqs, argSorts = x.MakeVarsForArgumentTerms ts
            let comb_var = x.CombVar argSorts
            let vars = (new_vars, comb_var)::vars
//            let vars = Map.add comb_var new_vars vars
            (eqs, Some(AApply(op, [comb_var]))), vars
        | Equal(t1, t2) -> ([t1, t2], None), vars
        | Distinct _ -> __unreachable__() // because diseq transformation has been performed before
        | Bot | Top as a -> ([], Some a), vars

    member private x.UnarifyAtoms = List.mapFold x.UnarifyAtom []

    member private x.UnarifyRule = function
        | Rule(_, body, head) ->
            let bodyEqsAndAtoms, vars = x.UnarifyAtoms body
            let bodyEqs, bodyAtoms = List.unzip bodyEqsAndAtoms
            let bodyAtoms = List.choose id bodyAtoms
            let (headEqs, headAtom), vars = x.UnarifyAtom vars head
            let eqs = headEqs @ List.concat bodyEqs
            let head = Option.defaultValue Bot headAtom
            match x.EquationsToPob vars eqs with
            | Some pobWithArgs ->
                let phis = x.AnswerMarkedPOB pobWithArgs
                Some <| Rule.clARule (phis @ bodyAtoms) head
            | None -> None

    member x.UnarifyRules rules = List.choose x.UnarifyRule rules

let synchronize commands =
    let commands, rules = List.choose2 (function OriginalCommand o -> Choice1Of2 o | TransformedCommand t -> Choice2Of2 t | LemmaCommand _ -> __unreachable__()) commands
    let adt_decls, commands = commands |> List.choose2 (function DeclareDatatype(a, b) -> Choice1Of2 [a, b] | DeclareDatatypes dts -> Choice1Of2 dts | c -> Choice2Of2 c)
    let adt_decls = List.concat adt_decls
    let adt_decls = adt_decls |> ADTExtensions.adtDefinitionsToRaw |> List.map (fun (s, cs) -> s, List.map (fun (c, ss) -> Operation.makeElementaryOperationFromVars c ss s) cs)
    let pobdb = POBDB(adt_decls)

    let commands = pobdb.UnarifyDeclarations commands
    let rules = pobdb.UnarifyRules rules
    let new_rules = pobdb.DumpRules ()

    let adt_decl_commands = pobdb.DumpADTRules ()

    List.map OriginalCommand (adt_decl_commands @ commands) @ new_rules @ List.map TransformedCommand rules
