module RInGen.Typer
open RInGen.Operations

let testerNameOf fname = Symbols.addPrefix "is-" fname
let testerOpOf testerName adtname = Operation.makeElementaryOperationFromSorts testerName [adtname] boolSort

type Typer(operations : Map<symbol, operation>, adts : Map<sort, (symbol * symbol) list>) =
    let operations = operations
    let adts = adts

    let makeConstructorTesterPair c t = c, t
    let takeConstructor (c, _) = c
    let takeTester (_, t) = t

    member x.tryFind opName = Map.tryFind opName operations
    member x.find opName = Map.find opName operations
    member x.addOperation name op = Typer(Map.add name op operations, adts)
    member x.addADTConstructors name nos =
        let names = Map.toList nos |> List.map (fun (c, _) -> makeConstructorTesterPair c (testerNameOf c))
        Typer(Map.union operations nos, Map.add name names adts)
    member x.containsKey key = Map.containsKey key operations
    member x.getConstructors adtName = Map.find adtName adts |> List.map takeConstructor
    member x.tryGetTesters adtName = Map.tryFind adtName adts |> Option.map (List.map takeTester)

    new (operations) = Typer(operations, Map.empty)

let rec typeOf = function
    | Not _
    | Hence _
    | And _
    | Or _
    | Forall _
    | Exists _
    | BoolConst _ -> boolSort
    | Number _ -> integerSort
    | Ident(_, t) -> t
    | Apply(op, _) -> Operation.returnType op
    | Match(_, (_, t)::_)
    | Ite(_, t, _)
    | Let(_, t) -> typeOf t
    | Match(_, []) -> __unreachable__()

let tryTypeCheck f (typer : Typer) = Option.map Operation.returnType (typer.tryFind f)

let tryGetOperation (typer : Typer) opName = typer.tryFind opName
let getOperation (typer : Typer) opName =
    match tryGetOperation typer opName with
    | Some r -> r
    | _ -> failwithf $"Unknown operation: {opName}"
let fillOperation (typer : Typer) opName argTypes =
    let op = getOperation typer opName
    fillDummyOperationTypes op argTypes

let addOperation name op (typer : Typer) = typer.addOperation name op

let empty = Typer(elementaryOperations)

let sort (_, sorts) name =
    match Map.tryFind name sorts with
    | Some s -> s
    | None -> name

let sort_list ts = List.map (sort ts)
let sorted_var ts (v, t) = v, sort ts t
let sorted_var_list ts vs = List.map (sorted_var ts) vs
let constructor ts (c, t) = c, sorted_var_list ts t
let constructor_list ts cs = List.map (constructor ts) cs
let definition ts (name, args, ret, body) = name, sorted_var_list ts args, sort ts ret, body

let addADTOperations (typer : Typer) adtname fname selectors =
    let constr_op = Operation.makeElementaryOperationFromVars fname selectors adtname
    let typer = List.fold (fun typer (pr, s) -> addOperation pr (Operation.makeElementaryOperationFromSorts pr [adtname] s) typer) typer selectors
    let typer = addOperation fname constr_op typer
    let testerName = testerNameOf fname
    let typer = addOperation testerName (testerOpOf testerName adtname) typer
    constr_op, typer

let notMapApply f z = function
    | Top -> z Bot
    | Bot -> z Top
//    | ANot e -> e
    | Equal(t1, t2) -> z <| Distinct(t1, t2)
    | Distinct(t1, t2) -> z <| Equal(t1, t2)
    | AApply(op, ts) -> f op ts

let rec nota (typer : Typer) =
    let notOperation op ts =
        match op, ts with
        | (NotT negop, ts) -> AApply(negop, ts) :: [] //TODO: approximates too much: see CHC-LIA-LIN-Arrays_001.smt2
        | (ElementaryOperation(testerName, [adtname], _), ([_] as args)) ->
            match typer.tryGetTesters adtname with
            | Some testers when List.contains testerName testers ->
                List.filter ((<>) testerName) testers |> List.map (fun name -> let op = typer.find name in AApply(op, args))
            | _ -> __notImplemented__()
    //    | AApply(UserDefinedOperation _, []) as e -> ANot e
    //    | AApply(UserDefinedOperation _, _) as e -> ANot e // TODO: failwithf "Trying to obtain negation of user defined predicate: %O" e
    //    | AAnd ts -> ts |> List.map nota |> AOr
    //    | AOr ts -> ts |> List.map nota |> AAnd
        | _ -> __notImplemented__()
    notMapApply notOperation List.singleton

let interpretCommand (typer : Typer) c =
    let extendDef (typer : Typer) (name, vars, sort, _) = addOperation name (Operation.makeUserOperationFromVars name vars sort) typer
    let extendDecl (typer : Typer) (adtname, cs) =
        let handle_constr (constrs, typer) (fname, vars) =
            let constr_op, typer = addADTOperations typer adtname fname vars
            Map.add fname constr_op constrs, typer
        let constrs, typer = List.fold handle_constr (Map.empty, typer) cs
        typer.addADTConstructors adtname constrs
    match c with
    | Definition(DefineFunRec df)
    | Definition(DefineFun df) -> extendDef typer df
    | Definition(DefineFunsRec dfs) -> dfs |> List.fold extendDef typer
    | Command(DeclareDatatype(name, cs)) -> extendDecl typer (name, cs)
    | Command(DeclareDatatypes dts) -> dts |> List.fold extendDecl typer
    | Command(DeclareConst(name, sort)) -> addOperation name (Operation.makeUserOperationFromSorts name [] sort) typer
    | Command(DeclareFun(name, argTypes, sort)) ->
        addOperation name (Operation.makeUserOperationFromSorts name argTypes sort) typer
    | Command(DeclareSort name) -> typer
    | _ -> typer

let typerMapFold f z cs =
    let rs, (_, z) = List.mapFold (fun (typer, z) c -> let typer = interpretCommand typer c in let r, z = f typer z c in r, (typer, z)) (empty, z) cs
    rs, z

let typerFold f cs =
    List.mapFold (fun typer c -> let typer = interpretCommand typer c in let r = f typer c in r, typer) empty cs |> fst