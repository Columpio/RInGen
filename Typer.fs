module FLispy.Typer
open FLispy.Operations
open FLispy.VarEnv

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

let tryTypeCheck f typer = Option.map Operation.returnType (Map.tryFind f typer)
let getOperation f typer =
    match Map.tryFind f typer with
    | Some r -> r
    | _ -> failwithf "Unknown type: %s" f
let typeGet x (typer, env) =
    match VarEnv.typeCheck env x with
    | Some t -> t
    | None ->
        match tryTypeCheck x typer with
        | Some t -> t
        | None -> failwithf "Unknown type: %s" x

let typerFold f z cs =
    let interpretCommand (typer, z) c =
        let extendDef typer (name, vars, sort, _) = Map.add name (Operation.makeUserOperationFromVars name vars sort) typer
        let extendDecl typer (adtname, cs) =
            let handle_constr typer (fname, vars) =
                let typer = List.fold (fun typer (pr, s) -> Map.add pr (Operation.makeElementaryOperationFromSorts pr [adtname] s) typer) typer vars
                Map.add fname (Operation.makeElementaryOperationFromVars fname vars adtname) typer
            List.fold handle_constr typer cs
        let typer =
            match c with
            | DefineFunRec df
            | DefineFun df -> extendDef typer df
            | DefineFunsRec dfs -> dfs |> List.fold extendDef typer
            | DeclareDatatype(name, cs) -> extendDecl typer (name, cs)
            | DeclareDatatypes dts -> dts |> List.fold extendDecl typer
            | DeclareConst(name, sort) -> Map.add name (Operation.makeUserOperationFromSorts name [] sort) typer
            | DeclareFun(name, argTypes, sort) -> Map.add name (Operation.makeUserOperationFromSorts name argTypes sort) typer
            | _ -> typer
        let r, z = f typer z c
        r, (typer, z)
    List.mapFold interpretCommand (elementaryOperations, z) cs |> fst

let typerMap f cs = typerFold (fun typer () c -> f typer c, ()) () cs
