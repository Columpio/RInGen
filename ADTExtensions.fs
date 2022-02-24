module RInGen.ADTExtensions

let isADTMatchPlaceholder s = s = "_"

let getFreeVarsFromPattern =
    let rec get_free_vars = function
        | Apply(_, ts) -> List.collect get_free_vars ts
        | Ident(v, t) -> [v, t]
        | _ -> __unreachable__()
    get_free_vars

let rec isGround = function
    | TApply(_, ts) -> List.forall isGround ts
    | _ -> false

let tryGetADTName = function
    | ADTSort name -> Some name
    | _ -> None

let getTesterNameFromConstructor constrBaseName =
    Symbols.addPrefix "is-" constrBaseName

let private generateConstructorAndTesterNames constrBaseName =
    let constrName = IdentGenerator.gensymp constrBaseName
    let testerName = IdentGenerator.gensymp <| getTesterNameFromConstructor constrBaseName
    constrName, testerName

let generateConstructorAndTesterOps constrBaseName selectorSorts adtSort =
    let cName, tName = generateConstructorAndTesterNames constrBaseName
    let selectorSorts = List.map (fun (selName, selSort) -> IdentGenerator.gensymp selName, selSort) selectorSorts
    Operation.makeADTOperations adtSort cName tName selectorSorts

let adtDefinitionToRaw (adt : datatype_def) : sort * (ident * (ident * sort) list) list = //TODO: remove it with refactoring
    let opsToIdents (c, _, ss) =
        let cName = Operation.opName c
        let cSorts = Operation.argumentTypes c
        let selNames = List.map Operation.opName ss
        cName, List.zip selNames cSorts
    let name, fs = adt
    let adtSort = ADTSort name
    adtSort, List.map opsToIdents fs

let adtDefinitionsToRaw = List.map adtDefinitionToRaw
