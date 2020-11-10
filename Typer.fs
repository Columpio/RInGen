module FLispy.Typer
open FLispy.Operations

let rec typeOf = function
    | Constant(Number _) -> "Int"
    | Forall _
    | Exists _
    | And _
    | Or _
    | Not _
    | Hence _
    | Constant(Bool _) -> "Bool"
    | Ident(_, t) -> t
    | Apply(op, _) -> Operation.returnType op
    | Match(_, ((_, t)::_))
    | Ite(_, t, _)
    | Let(_, t) -> typeOf t
    | Match(_, []) -> __unreachable__()

let tryTypeCheck f (typer, _) = Option.map Operation.returnType (Map.tryFind f typer)
let getOperation f (typer, _) =
    match Map.tryFind f typer with
    | Some r -> r
    | _ -> failwithf "Unknown type: %s" f

let addOperationsOps name op ops = Map.add name op ops
let addOperation name op (ops, sorts) = addOperationsOps name op ops, sorts

let addSort name (ops, sorts) = ops, Map.add name IntToNat.nat_sort sorts

let empty = elementaryOperations, Map.empty

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

let typerFold f z cs =
    let interpretCommand ((typer, sorts) as typs, z) c =
        let extendDef typer (name, vars, sort, _) = addOperationsOps name (Operation.makeUserOperationFromVars name vars sort) typer
        let extendDecl typer (adtname, cs) =
            let handle_constr typer (fname, vars) =
                let typer = List.fold (fun typer (pr, s) -> Map.add pr (Operation.makeElementaryOperationFromSorts pr [adtname] s) typer) typer vars
                Map.add fname (Operation.makeElementaryOperationFromVars fname vars adtname) typer
            List.fold handle_constr typer cs
        let typer =
            match c with
            | DefineFunRec df
            | DefineFun df -> extendDef typer df, sorts
            | DefineFunsRec dfs -> dfs |> List.fold extendDef typer, sorts
            | DeclareDatatype(name, cs) -> extendDecl typer (name, cs), sorts
            | DeclareDatatypes dts -> dts |> List.fold extendDecl typer, sorts
            | DeclareConst(name, sort) -> addOperationsOps name (Operation.makeElementaryOperationFromSorts name [] sort) typer, sorts
            | DeclareFun(name, argTypes, sort) -> addOperationsOps name (Operation.makeUserOperationFromSorts name argTypes sort) typer, sorts
            | DeclareSort name -> addSort name typs
            | _ -> typs
        let r, z = f typer z c
        r, (typer, z)
    List.mapFold interpretCommand (empty, z) cs |> fst

let typerMap f cs = typerFold (fun typer () c -> f typer c, ()) () cs
