module Tests.Transformations
open NUnit.Framework
open RInGen

[<TestFixture>]
type SamplesTests () =
    inherit FileTransformationTester("samples")

    [<Test>]
    member x.LtLtOrigTest () =
        let config path outPath = $"-o {outPath} transform --mode original {path} -t"
        x.RunTest "ltlt.smt2" ".orig" config

    [<Test>]
    member x.LemmaOrigTest () =
        let config path outPath = $"-o {outPath} transform --mode original {path} -t"
        x.RunTest "lemmas_with_new_syntax.smt2" "" config

    [<Test>]
    member x.LtLtTTATest () =
        let config path outPath = $"-o {outPath} transform --mode freesorts {path} -t --tta-transform"
        x.RunTest "ltlt.smt2" ".tta" config

[<TestFixture>]
type TIPTests () =
    inherit DirectoryTransformationTester("TIP")

    [<Test>]
    member x.OriginalTrans () =
        let name = "OriginalTrans"
        let config origPath outPath = $"-o {outPath} transform --mode original {origPath} -t --tip"
        x.RunTest name config

[<TestFixture>]
type TTATests () =
    [<Test>]
    member x.evenEmptyPattern () =
        let ttaTraverser = TtaTransform.ToTTATraverser(1)
        let natAdt = ADTSort("nat")
        let zConstr = Operation.makeElementaryOperationFromSorts "Z" [] natAdt
        let pred = Operation.makeUserRelationFromSorts "isEven" [natAdt]
        let xs = [TApply(zConstr, [])]
        let automaton = ttaTraverser.GetOrAddApplicationAutomaton pred xs
        let decls = List.map toString automaton.Declarations
        ()

    [<Test>]
    member x.evenSSPattern () =
        let ttaTraverser = TtaTransform.ToTTATraverser(1)
        let natAdt = ADTSort("nat")
        let sConstr = Operation.makeElementaryOperationFromSorts "S" [natAdt] natAdt
        let pred = Operation.makeUserRelationFromSorts "isEven" [natAdt]
        let xs = [TApply(sConstr, [TApply(sConstr, [TIdent("x", natAdt)])])]
        let automaton = ttaTraverser.GetOrAddApplicationAutomaton pred xs
        let decls = List.map toString automaton.Declarations
        ()

    [<Test>]
    member x.ltZSPattern () =
        let ttaTraverser = TtaTransform.ToTTATraverser(1)
        let natAdt = ADTSort("nat")
        let zConstr = Operation.makeElementaryOperationFromSorts "Z" [] natAdt
        let sConstr = Operation.makeElementaryOperationFromSorts "S" [natAdt] natAdt
        let pred = Operation.makeUserRelationFromSorts "isEven" [natAdt]
        let xs = [TApply(zConstr, []); TApply(sConstr, [TApply(sConstr, [TIdent("x", natAdt)])])]
        let automaton = ttaTraverser.GetOrAddApplicationAutomaton pred xs
        let decls = List.map toString automaton.Declarations
        ()

    [<Test>]
    member x.patternDelayNode () =
        let ttaTraverser = TtaTransform.ToTTATraverser(2)
        let treeAdt = ADTSort("tree")
        let nodeConstr = Operation.makeElementaryOperationFromSorts "Node" [treeAdt; treeAdt] treeAdt
        let pred = Operation.makeUserRelationFromSorts "ltlefttree" [treeAdt; treeAdt]
        let xs = [TIdent("x", treeAdt); TApply(nodeConstr, [TIdent("y", treeAdt); TIdent("z", treeAdt)])]
        let automaton = ttaTraverser.GetOrAddApplicationAutomaton pred xs
        let decls = List.map toString automaton.Declarations
        ()

    [<Test>]
    member x.patternNodeNode () =
        let ttaTraverser = TtaTransform.ToTTATraverser(2)
        let treeAdt = ADTSort("tree")
        let nodeConstr = Operation.makeElementaryOperationFromSorts "Node" [treeAdt; treeAdt] treeAdt
        let pred = Operation.makeUserRelationFromSorts "ltlefttree" [treeAdt; treeAdt]
        let xs = [TApply(nodeConstr, [TIdent("v", treeAdt); TIdent("w", treeAdt)]); TApply(nodeConstr, [TIdent("x", treeAdt); TIdent("y", treeAdt)])]
        let automaton = ttaTraverser.GetOrAddApplicationAutomaton pred xs
        let decls = List.map toString automaton.Declarations
        ()
    [<Test>]
    member x.patternLeafNode () =
        let ttaTraverser = TtaTransform.ToTTATraverser(2)
        let treeAdt = ADTSort("tree")
        let leafConstr =  Operation.makeElementaryOperationFromSorts "Leaf" [] treeAdt
        let nodeConstr = Operation.makeElementaryOperationFromSorts "Node" [treeAdt; treeAdt] treeAdt
        let pred = Operation.makeUserRelationFromSorts "ltlefttree" [treeAdt; treeAdt]
        let xs = [TApply(leafConstr, []); TApply(nodeConstr, [TIdent("x", treeAdt); TIdent("y", treeAdt)])]
        let automaton = ttaTraverser.GetOrAddApplicationAutomaton pred xs
        let decls = List.map toString automaton.Declarations
        ()

    [<Test>]
    member x.patternLeafLeaf () =
        let ttaTraverser = TtaTransform.ToTTATraverser(2)
        let treeAdt = ADTSort("tree")
        let leafConstr =  Operation.makeElementaryOperationFromSorts "Leaf" [] treeAdt
        let pred = Operation.makeUserRelationFromSorts "ltlefttree" [treeAdt; treeAdt]
        let xs = [TApply(leafConstr, []); TApply(leafConstr, [])]
        let automaton = ttaTraverser.GetOrAddApplicationAutomaton pred xs
        let decls = List.map toString automaton.Declarations
        ()
