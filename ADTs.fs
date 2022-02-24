module RInGen.ADTs
open Relativization
open SubstituteOperations
open Rule

module SupplementaryADTAxioms =
    let private generateSelectors adtSort constructors selectorsMap =
        // car(x, r) <- x = cons(r, a)
        let generateSelectorForConstructor selectorsMap (constructorName, selectorsWithTypes) =
            let constructorOp = Operation.makeElementaryOperationFromVars constructorName selectorsWithTypes adtSort
            let constrArgs = Terms.generateVariablesFromOperation constructorOp
            let adtArg = Term.generateVariable adtSort
            let selectorPremise = [Equal(adtArg, TApply(constructorOp, constrArgs))]
            let generateSelector selectorsMap (retArg, (selectorName, selectorType)) =
                let relselectorName = IdentGenerator.gensymp selectorName
                let op = Operation.makeElementaryOperationFromSorts selectorName [adtSort] selectorType
                let relselectorOp = Operation.makeElementaryOperationFromSorts relselectorName [adtSort] selectorType |> Relativization.relativizeOperation
                let decl = Relativization.reldeclare relselectorName [adtSort] selectorType
                let body = clARule selectorPremise (relapply relselectorOp [adtArg] retArg)
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
        let testerName = ADTExtensions.getTesterNameFromConstructor constructorName
        let relTesterName = IdentGenerator.gensymp testerName
        let op = Operation.makeElementaryRelationFromSorts testerName [sort]
        let relOp = Operation.makeElementaryRelationFromSorts relTesterName [sort]
        let decl = DeclareFun(relTesterName, [sort], BoolSort)
        relOp, decl, addShouldNotRelativize op relOp substs

    let private generateTesterBody tester_op constructor_op sort =
        let constructorVars = Terms.generateVariablesFromOperation constructor_op
        clARule [] (AApply(tester_op, [Term.apply constructor_op constructorVars]))

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
        let decl = DeclareFun(diseq_name, [name; name], BoolSort)
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
        let diseq = Atom.apply2 diseq_op
        let facts = seq {
            for l, r in Seq.nondiag cs do
                let lids = Terms.generateVariablesFromOperation l
                let rids = Terms.generateVariablesFromOperation r
                yield clAFact (diseq (Term.apply l lids) (Term.apply r rids))
        }
        let steps = seq {
            for constr in cs do
                let lids = Terms.generateVariablesFromOperation constr
                let rids = Terms.generateVariablesFromOperation constr
                let app = diseq (Term.apply constr lids) (Term.apply constr rids)
                for sort, l, r in List.zip3 (Operation.argumentTypes constr) lids rids do
                    match Map.tryFind sort diseqs with
                    | Some op -> yield clARule [AApply(op, [l; r])] app
                    | None -> yield clARule [Distinct(l, r)] app
        }
        Seq.append facts steps |> List.ofSeq

    let private generateEqBody eq_op _ _ adtSort =
        // Nat = Z | S Nat
        // eqNat(x, x)
        // List = Nil | Cons(Nat, List)
        // eqList(x, x)
        let xid = Term.generateVariable adtSort
        [clAFact (AApply(eq_op, [xid; xid]))]

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
        | OriginalCommand(DeclareDatatype dt) ->
            let (decls, defs), acc = generateDefinitionsFromDatatype acc (ADTExtensions.adtDefinitionToRaw dt)
            decls @ defs, acc
        | OriginalCommand(DeclareDatatypes dts) ->
            let cs, acc = List.mapFold generateDefinitionsFromDatatype acc (ADTExtensions.adtDefinitionsToRaw dts)
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
    let op = Operation.makeElementaryRelationFromSorts diseq_name [BoolSort; BoolSort]
    let diseq = Atom.apply2 op
    let decl = DeclareFun(diseq_name, [BoolSort; BoolSort], BoolSort)
    decl, diseq, op

let generateBoolCongruences eqs diseqs =
    match Map.tryFind BoolSort eqs, Map.tryFind BoolSort diseqs with
    | Some eq, Some diseq -> Atom.apply2 eq, Atom.apply2 diseq, eqs, diseqs, []
    | _ ->
        let eqDecl, eq, eqOp = generateBoolCongruenceHeader "eq"
        let diseqDecl, diseq, diseqOp = generateBoolCongruenceHeader "diseq"
        let xid = Term.generateVariable BoolSort
        let eqRules = [OriginalCommand eqDecl; TransformedCommand <| clAFact (eq xid xid)]
        let diseqBody = [
            clAFact (diseq Term.truth Term.falsehood)
            clAFact (diseq Term.falsehood Term.truth)
        ]
        let diseqRules = OriginalCommand diseqDecl :: List.map TransformedCommand diseqBody
        eq, diseq, Map.add BoolSort eqOp eqs, Map.add BoolSort diseqOp diseqs, eqRules @ diseqRules