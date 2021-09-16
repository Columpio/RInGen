module RInGen.ADTs
open Relativization
open SubstituteOperations

module SupplementaryADTAxioms =
    let private generateSelectors adtSort constructors selectorsMap =
        // car(x, r) <- x = cons(r, a)
        let generateSelectorForConstructor selectorsMap (constructorName, selectorsWithTypes) =
            let constructorOp = Operation.makeElementaryOperationFromVars constructorName selectorsWithTypes adtSort
            let constrArgs = Operation.generateArguments constructorOp
            let adtArg = IdentGenerator.gensym (), adtSort
            let selectorVars = adtArg::constrArgs
            let selectorPremise = [Equal(TIdent adtArg, TApply(constructorOp, List.map TIdent constrArgs))]
            let generateSelector selectorsMap (retArg, (selectorName, selectorType)) =
                let relselectorName = IdentGenerator.gensymp selectorName
                let op = Operation.makeElementaryOperationFromSorts selectorName [adtSort] selectorType
                let relselectorOp = Operation.makeElementaryOperationFromSorts relselectorName [adtSort] selectorType |> Relativization.relativizeOperation
                let decl = Relativization.reldeclare relselectorName [adtSort] selectorType
                let body = rule selectorVars selectorPremise (AApply(relselectorOp, [TIdent retArg; TIdent adtArg]))
                (OriginalCommand decl, TransformedCommand body), addShouldRelativize op relselectorOp selectorsMap
            let comms, selectorsMap =
                selectorsWithTypes
                |> List.zip constrArgs
                |> List.mapFold generateSelector selectorsMap
            List.unzip comms, selectorsMap
        let comms, selectorsMap = List.mapFold generateSelectorForConstructor selectorsMap constructors
        let decls, defs = List.unzip comms
        List.concat decls, List.concat defs, selectorsMap

    let private generateTesterHeader substs sort constructorName =
        let testerName = Typer.testerNameOf constructorName
        let relTesterName = IdentGenerator.gensymp testerName
        let op = Operation.makeElementaryRelationFromSorts testerName [sort]
        let relOp = Operation.makeElementaryRelationFromSorts relTesterName [sort]
        let decl = DeclareFun(relTesterName, [sort], boolSort)
        relOp, decl, addShouldNotRelativize op relOp substs

    let applyConstructor op xs = TApply(op, xs)

    let private generateTesterBody tester_op constructor_op sort =
        let constructorVars = Operation.generateArguments constructor_op
        rule constructorVars [] (AApply(tester_op, [applyConstructor constructor_op (List.map TIdent constructorVars)]))

    let private generateTesters sort cs substs =
        let generateTester substs (constructorName : symbol, selectorsWithTypes) =
            let op, decl, substs = generateTesterHeader substs sort constructorName
            let body = generateTesterBody op (Operation.makeElementaryOperationFromVars constructorName selectorsWithTypes sort) sort
            (OriginalCommand decl, TransformedCommand body), substs
        let cs, substs = List.mapFold generateTester substs cs
        let decls, defs = List.unzip cs
        decls, defs, substs

    let private generateCongruenceHeader congrBaseName diseqs name =
        let diseq_name = IdentGenerator.gensymp (congrBaseName + (Sort.sortToFlatString name))
        let op = Operation.makeElementaryRelationFromSorts diseq_name [name; name]
        let decl = DeclareFun(diseq_name, [name; name], boolSort)
        op, Map.add name op diseqs, decl

    let private generateDiseqBody diseq_op diseqs cs adtSort =
        // Nat = Z | S Nat
        // diseqNat(Z, S y)
        // diseqNat(S x, Z)
        // diseqNat(x, y) -> diseqNat(S x, S y)
        // List = Nil | Cons(Nat, List)
        // diseqList(Nil, Cons(x, l))
        // diseqList(Cons(x, l), Nil)
        // diseqNat(x, y) -> diseqList(Cons(x, l1), Cons(y, l2))
        // diseqList(l1, l2) -> diseqList(Cons(x, l1), Cons(y, l2))
        let cs = cs |> List.map (fun (name, selectorsWithTypes) -> Operation.makeElementaryOperationFromVars name selectorsWithTypes adtSort)
        let diseq x y = AApply(diseq_op, [x; y])
        let apply = applyConstructor
        let facts = seq {
            for l, r in Seq.nondiag cs do
                let lvars = Operation.generateArguments l
                let rvars = Operation.generateArguments r
                let lids = lvars |> List.map TIdent
                let rids = rvars |> List.map TIdent
                yield rule (lvars @ rvars) [] (diseq (apply l lids) (apply r rids))
        }
        let steps = seq {
            for constr in cs do
                let lvars = Operation.generateArguments constr
                let rvars = Operation.generateArguments constr
                let lids = lvars |> List.map TIdent
                let rids = rvars |> List.map TIdent
                let app = diseq (apply constr lids) (apply constr rids)
                for sort, l, r in List.zip3 (Operation.argumentTypes constr) lids rids do
                    match Map.tryFind sort diseqs with
                    | Some op -> yield rule (lvars @ rvars) [AApply(op, [l; r])] app
                    | None -> yield rule (lvars @ rvars) [Distinct(l, r)] app
        }
        Seq.append facts steps |> List.ofSeq

    let private generateEqBody eq_op _ _ adtSort =
        // Nat = Z | S Nat
        // eqNat(x, x)
        // List = Nil | Cons(Nat, List)
        // eqList(x, x)
        let x = IdentGenerator.gensym (), adtSort
        let xid = TIdent x
        [rule [x] [] (AApply(eq_op, [xid; xid]))]

    let private generateCongruence congrBaseName generateCongruenceBody name constrs diseqs =
        let op, diseqs, decl = generateCongruenceHeader congrBaseName diseqs name
        let body = generateCongruenceBody op diseqs constrs name
        OriginalCommand decl, List.map TransformedCommand body, diseqs
    let private generateDiseqs = generateCongruence "diseq" generateDiseqBody
//    let private generateEqs = generateCongruence "eq" generateEqBody

    let private generateDefinitionsFromDatatype (substs, eqs, diseqs) (name, constrs) =
        let selectorDeclarations, selectorDefinitions, substs = generateSelectors name constrs substs
        let testerDeclarations, testerDefinitions, substs = generateTesters name constrs substs
        let diseqDeclaration, diseqDefinitions, diseqs = generateDiseqs name constrs diseqs
//        let eqDeclaration, eqDefinitions, eqs = generateEqs name constrs eqs
        let decls = diseqDeclaration :: selectorDeclarations @ testerDeclarations
        let defs = selectorDefinitions @ testerDefinitions @ diseqDefinitions
        (decls, defs), (substs, eqs, diseqs)

    let private substituteSymbols acc = function
        | OriginalCommand(DeclareDatatype(name, constrs)) ->
            let (decls, defs), acc = generateDefinitionsFromDatatype acc (name, constrs)
            decls @ defs, acc
        | OriginalCommand(DeclareDatatypes dts) ->
            let cs, acc = List.mapFold generateDefinitionsFromDatatype acc dts
            let decls, defs = List.unzip cs
            List.concat (decls @ defs), acc
        | _ -> [], acc

    let addSupplementaryAxiomsIncremental (eqs, diseqs) commands =
        let commands, (rels, eqs, diseqs) = List.mapFold (fun sd c -> let cs, sd = substituteSymbols sd c in c::cs, sd) (Map.empty, eqs, diseqs) commands
        let commands = List.concat commands
        let relativizer = SubstituteOperations(rels, eqs, diseqs)
        List.map relativizer.SubstituteOperationsWithRelations commands, (eqs, diseqs)

    let addSupplementaryAxioms commands = addSupplementaryAxiomsIncremental (Map.empty, Map.empty) commands

let private generateBoolCongruenceHeader congrName =
    let diseq_name = IdentGenerator.gensymp (congrName + "Bool")
    let op = Operation.makeElementaryRelationFromSorts diseq_name [boolSort; boolSort]
    let diseq = applyBinaryRelation op
    let decl = DeclareFun(diseq_name, [boolSort; boolSort], boolSort)
    decl, diseq, op

let generateBoolCongruences eqs diseqs =
    match Map.tryFind boolSort eqs, Map.tryFind boolSort diseqs with
    | Some eq, Some diseq -> applyBinaryRelation eq, applyBinaryRelation diseq, eqs, diseqs, []
    | _ ->
        let eqDecl, eq, eqOp = generateBoolCongruenceHeader "eq"
        let diseqDecl, diseq, diseqOp = generateBoolCongruenceHeader "diseq"
        let x = IdentGenerator.gensym (), boolSort
        let xid = TIdent x
        let eqRules = [OriginalCommand eqDecl; TransformedCommand <| rule [x] [] (eq xid xid)]
        let diseqBody = [
            rule [] [] (diseq truet falset)
            rule [] [] (diseq falset truet)
        ]
        let diseqRules = OriginalCommand diseqDecl :: List.map TransformedCommand diseqBody
        eq, diseq, Map.add boolSort eqOp eqs, Map.add boolSort diseqOp diseqs, eqRules @ diseqRules