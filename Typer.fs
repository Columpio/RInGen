module RInGen.Typer
open RInGen.Operations

type Typer(operations : Map<symbol, operation>, adts : Map<sort, symbol list>) =
    let operations = operations
    let adts = adts

    member x.tryFind opName = Map.tryFind opName operations
    member x.find opName = Map.find opName operations
    member x.addOperation name op = Typer(Map.add name op operations, adts)
    member x.addADTConstructors name nos =
        let names = Map.toList nos |> List.map fst
        Typer(Map.union operations nos, Map.add name names adts)
    member x.containsKey key = Map.containsKey key operations
    member x.getConstructors adtName = Map.find adtName adts

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
    | Match(_, ((_, t)::_))
    | Ite(_, t, _)
    | Let(_, t) -> typeOf t
    | Match(_, []) -> __unreachable__()

let tryTypeCheck f (typer : Typer) = Option.map Operation.returnType (typer.tryFind f)

let getOperation (typer : Typer) opName =
    match typer.tryFind opName with
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

let interpretCommand (typer : Typer) c =
    let extendDef (typer : Typer) (name, vars, sort, _) = addOperation name (Operation.makeUserOperationFromVars name vars sort) typer
    let extendDecl (typer : Typer) (adtname, cs) =
        let handle_constr (constrs, typer) (fname, vars) =
            let typer = List.fold (fun (typer : Typer) (pr, s) -> typer.addOperation pr (Operation.makeElementaryOperationFromSorts pr [adtname] s)) typer vars
            let op = Operation.makeElementaryOperationFromVars fname vars adtname
            Map.add fname op constrs, typer
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