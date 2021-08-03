module RInGen.Synchronization
open System.Collections.Generic
open RInGen.IdentGenerator

type private POB = term list list

let private combineNames ns = join "" ns |> gensyms

let private topFreeVarsOf (pob : POB) = List.collect (List.choose (function TIdent(v, s) -> Some(v, s) | _ -> None)) pob |> Set.ofList |> Set.toList

let private uniformizeVars pob =
    let mutable n = 0
    let varMap = Dictionary()
    let rec substInTerm = function
        | TConst _ as c -> c
        | TIdent(i, s) ->
            match Dictionary.tryGetValue i varMap with
            | Some iSubst -> TIdent(iSubst, s)
            | None ->
            let newIndex = $"x{n}"
            varMap.Add(i, newIndex)
            n <- n + 1
            TIdent(newIndex, s)
        | TApply(id, ts) -> TApply(id, List.map substInTerm ts)
    List.map (List.map substInTerm) pob

let private substInTermWithPair v t u =
    let rec substInTermWithPair = function
        | TConst _ as c -> c
        | TIdent(v1, s1) as vs1 -> if v = (v1, s1) then t else vs1
        | TApply(op, ts) -> TApply(op, List.map substInTermWithPair ts)
    substInTermWithPair u
let rec private substInTerm substVarsMap = function
    | TConst _ as c -> c
    | TIdent(i, s) as v -> Map.tryFind (i, s) substVarsMap |> Option.defaultValue v
    | TApply(id, ts) -> TApply(id, substInTermList substVarsMap ts)
and private substInTermList substVarsMap = List.map (substInTerm substVarsMap)

let private substVars substVarsMap pob =
    List.map (substInTermList substVarsMap) pob

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
        match Dictionary.tryGetValue sorts comb_sorts with
        | Some comb_sort -> comb_sort
        | None ->
        let new_sort = sorts |> List.map (function PrimitiveSort i -> i | _ -> __notImplemented__()) |> combineNames |> PrimitiveSort
        x.RegisterCombinedSort sorts new_sort
        new_sort

    member private x.CombConstrName constrNames argSorts =
        match Dictionary.tryGetValue constrNames comb_constructors with
        | Some combinedName -> combinedName
        | None ->
        let names = List.map Operation.opName constrNames
        let retSorts = List.map Operation.returnType constrNames
        let combinedName = combineNames names
        let combinedReturnSort = x.CombSort retSorts
        let op = Operation.makeElementaryOperationFromSorts combinedName argSorts combinedReturnSort
        comb_constructors.Add(constrNames, op)
        op

    member private x.CombVar sorts =
        let sort = x.CombSort sorts
        TIdent(gensym (), sort)

    member private x.RegisterPOB(pob) : operation =
        let pident = IdentGenerator.gensymp "phi"
        let sorts = List.map x.TypeOfCombinedTerm pob
        let op = Operation.makeElementaryRelationFromSorts pident sorts
        pobs.Add(pob, op)
        if IN_EXTRA_VERBOSE_MODE () then printfn $"""registered {op}: {pob |> List.map (List.map toString >> join ", " >> sprintf "(%s)") |> join "; "}"""
        op

    member private x.TryGetPOB(pob) : operation option = Dictionary.tryGetValue pob pobs

    member private x.AddCombRule pred rule =
        match Dictionary.tryGetValue pred rules with
        | Some predRules ->
            rules.[pred] <- rule::predRules
        | None -> rules.Add(pred, [rule])

    member private x.PossibleTerms sorts =
        let instantiateConstructorSignature constrOp =
            let vars = constrOp |> Operation.argumentTypes |> List.map (fun sort -> IdentGenerator.gensym (), sort)
            TApply(constrOp, List.map TIdent vars)
        let possibleTermsOfSort sort =
            let constrsSigns = adt_declarations.[sort]
            let possibleTerms = constrsSigns |> List.map instantiateConstructorSignature
            possibleTerms
        let possibleTermsOfEach = sorts |> List.map possibleTermsOfSort
        product possibleTermsOfEach

    member private x.TypeOfCombinedTerm ts = List.map typeOfTerm ts |> x.CombSort

    member private x.CombConstr(constrNames, args) =
        let argSorts = List.map typeOfTerm args
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
                let v = TIdent(IdentGenerator.gensym (), x.TypeOfCombinedTerm ts)
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
                let rawSubstPob = substVars substVarsMap pob // (Cons #4 Nil, Nil, Cons #4 Nil), (Nil, Nil, Nil)
                let argumentPob, argumentVars, predicateHeadArguments = x.CutHeadConstructors rawSubstPob
                yield argumentPob, argumentVars, predicateHeadArguments
        }

    member x.DumpRules () =
        // close rules with forall
        // generate declarations
        // return
        let ops, rules = rules |> Dictionary.toList |> List.unzip
        let rules = rules |> List.map List.rev |> List.concat |> List.map x.MakeClosedRule
        let decls = List.map Operation.declareOp ops
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
        let argPobAndVarsAndFreeVars = List.map (fun ((pob, _) as pvs) -> pvs, x.CollectFreeVarsInTerms pob |> Set.ofList) argumentPobAndVars
        let rec splitIntoClasses freeVars pvs done_pvss queue = function
            | [] -> splitEntry (pvs :: done_pvss) queue
            | (nxtPV, nxtFV)::rest ->
                if Set.intersect freeVars nxtFV |> Set.isEmpty then
                    splitIntoClasses freeVars pvs done_pvss ((nxtPV, nxtFV)::queue) rest
                else splitIntoClasses (Set.union freeVars nxtFV) (nxtPV::pvs) done_pvss queue rest
        and splitEntry done_pvss = function
            | [] -> done_pvss
            | (pv, freeVars)::rest -> splitIntoClasses freeVars [pv] done_pvss [] rest
        let splitedPobsAndArgs = splitEntry [] argPobAndVarsAndFreeVars
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

    member private x.UnifyTermsWith preferredForSubstitutionVars unifier t1 t2 : Map<sorted_var, term> option =
        // invariant:   `unifier` maps x |-> t, such that domain(unifier) ∩ FV(range(unifier)) = ∅
        //              so `substInTerm unifier` returns term `t` with FV(t) ∩ domain(unifier) = ∅
        let rec occursIn v s = function
            | TConst _ -> false
            | TIdent(v2, s2) -> v = v2 && s = s2
            | TApply(_, ts) -> List.exists (occursIn v s) ts
        let addToUnifier unifier v t =
            // invariant:   ({v} ∪ FV(t)) ∩ domain(unifier) = ∅ and {v} ∩ FV(t) = ∅
            // unifier' = unifier ∪ [v |-> t]
            // domain(unifier') ∩ FV(range(unifier')) = (domain(unifier) ∪ {v}) ∩ (FV(range(unifier)) ∪ FV(t)) = {v} ∩ FV(range(unifier))
            unifier
            |> Map.map (fun _ -> substInTermWithPair v t)
            |> Map.add v t
        let rec unifyTermsWith unifier (t1, t2) =
            if t1 = t2 then Some unifier else
            let t1 = substInTerm unifier t1
            let t2 = substInTerm unifier t2
            if t1 = t2 then Some unifier else
            match t1, t2 with
            | TIdent(v1, s1), TIdent(v2, s2) ->
                let vs1 = v1, s1
                let vs2 = v2, s2
                let v, t =
                    match Set.contains vs1 preferredForSubstitutionVars, Set.contains vs2 preferredForSubstitutionVars with
                    | true, false -> vs1, t2
                    | false, true -> vs2, t1
                    | _ -> if v1 < v2 then vs2, t1 else vs1, t2
                Some <| addToUnifier unifier v t
            | TIdent(v, s), (TApply _ as a)
            | (TApply _ as a), TIdent(v, s) ->
                if occursIn v s a then None else Some <| addToUnifier unifier (v, s) a
            | TIdent(v, s), (TConst _ as a)
            | (TConst _ as a), TIdent(v, s) -> Some <| addToUnifier unifier (v, s) a
            | TApply(op1, ts1), TApply(op2, ts2) ->
                if op1 <> op2 then None
                else List.foldChoose unifyTermsWith unifier (List.zip ts1 ts2)
            | _ -> None
        unifyTermsWith unifier (t1, t2)

    member private x.CollectFreeVarsInTerm = function
        | TIdent(i, s) -> [i, s]
        | TConst _ -> []
        | TApply(_, ts) -> x.CollectFreeVarsInTerms ts
    member private x.CollectFreeVarsInTerms = List.collect x.CollectFreeVarsInTerm

    member private x.CollectFreeVarsInAtom = function
        | AApply(_, ts) -> x.CollectFreeVarsInTerms ts
        | Equal _ | Distinct _ -> __unreachable__()
        | _ -> []

    member private x.EquationsToPob vars eqs : (term list * term) list option =
        // for `vars` mapping x |-> (v, [..,x,..]) unify all `eqs` and make one single POB with `v` variables near each query tuple
        let substVar unifier v = Option.defaultValue (TIdent v) <| Map.tryFind v unifier
        let componentVars = vars |> List.collect fst |> Set.ofList
        opt {
            let! unifier = List.foldChoose (fun unifier (t1, t2) -> x.UnifyTermsWith componentVars unifier t1 t2) Map.empty eqs
            let pob = vars |> List.map (fun (vars, v) -> List.map (substVar unifier) vars, v)
            return pob
        }

    member private x.UnarifyOperation = function
        | ElementaryOperation(name, args, ret) -> ElementaryOperation(name, [x.CombSort args], ret)
        | UserDefinedOperation(name, args, ret) -> UserDefinedOperation(name, [x.CombSort args], ret)

    member private x.MakeVarsForArgumentTerms ts =
        let makeVarForArgument t sort =
            let vs = gensym (), sort
            vs, (t, TIdent vs)

        let argSorts = List.map typeOfTerm ts
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
        | Top | Bot as a -> ([], Some a), vars

    member private x.MakeClosedRule(body, head) : rule =
        // forall quantifiers around all vars
        let freeVars = head::body |> List.collect x.CollectFreeVarsInAtom |> Set.ofList |> Set.toList
        rule freeVars body head

    member private x.UnarifyAtoms = List.mapFold x.UnarifyAtom

    member private x.UnarifyRule = function
        | ForallRule(_, r) -> x.UnarifyRule r
        | ExistsRule _ -> __unreachable__()
        | BaseRule(body, head) ->
            let bodyEqsAndAtoms, vars = x.UnarifyAtoms [] body
            let bodyEqs, bodyAtoms = List.unzip bodyEqsAndAtoms
            let bodyAtoms = List.choose id bodyAtoms
            let (headEqs, headAtom), vars = x.UnarifyAtom vars head
            let eqs = headEqs @ List.concat bodyEqs
            let head = Option.defaultValue Bot headAtom
            match x.EquationsToPob vars eqs with
            | Some pobWithArgs ->
                let phis = x.AnswerMarkedPOB pobWithArgs
                Some <| x.MakeClosedRule(phis @ bodyAtoms, head)
            | None -> None

    member x.UnarifyRules rules = List.choose x.UnarifyRule rules

let synchronize commands =
    let commands, rules = List.choose2 (function OriginalCommand o -> Choice1Of2 o | TransformedCommand t -> Choice2Of2 t) commands
    let adt_decls, commands = commands |> List.choose2 (function DeclareDatatype(a, b) -> Choice1Of2 [a, b] | DeclareDatatypes dts -> Choice1Of2 dts | c -> Choice2Of2 c)
    let adt_decls = List.concat adt_decls
    let adt_decls = adt_decls |> List.map (fun (s, cs) -> s, List.map (fun (c, ss) -> Operation.makeElementaryOperationFromVars c ss s) cs)
    let pobdb = POBDB(adt_decls)

    let commands = pobdb.UnarifyDeclarations commands
    let rules = pobdb.UnarifyRules rules
    let new_rules = pobdb.DumpRules ()

    let adt_decl_commands = pobdb.DumpADTRules ()

    List.map OriginalCommand (adt_decl_commands @ commands) @ new_rules @ List.map TransformedCommand rules
