module Tests.Transformations
open NUnit.Framework
open RInGen
open SMTLIB2

[<TestFixture>]
type SamplesTests () =
    inherit FileTransformationTester("samples")

    [<Test; Ignore("transformation tests do not work yet")>]
    member x.LtLtOrigTest () =
        let config path outPath = $"-o {outPath} transform --mode original {path} -t"
        x.RunTest "ltlt.smt2" ".orig" config

    [<Test; Ignore("transformation tests do not work yet")>]
    member x.LemmaOrigTest () =
        let config path outPath = $"-o {outPath} transform --mode original {path} -t"
        x.RunTest "lemmas_with_new_syntax.smt2" "" config

    [<Test; Ignore("transformation tests do not work yet")>]
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

module private PatternConstructor =
    let constructor = Operation.makeElementaryOperationFromSorts
    let zeroaryTerm name sort = Term.apply0 <| constructor name [] sort
    let unaryConstr name argSort retSort = Term.apply1 <| constructor name [argSort] retSort
    let binaryConstr name argSort1 argSort2 retSort =
        Term.apply2 <| constructor name [argSort1; argSort2] retSort

    let predicate name argSorts = Operation.makeUserRelationFromSorts name argSorts

    let nat = ADTSort("nat")
    let Z = zeroaryTerm "Z" nat
    let S = unaryConstr "S" nat nat

    let tree = ADTSort("tree")
    let leaf = zeroaryTerm "Leaf" tree
    let node = binaryConstr "Node" tree tree tree

    let nNat = TIdent("n", nat)
    let xTree, yTree, zTree = TIdent("x", tree), TIdent("y", tree), TIdent("z", tree)
    let vTree, wTree = TIdent("v", tree), TIdent("w", tree)

open PatternConstructor
[<TestFixture>]
type TTATests () =
    [<Test>]
    member x.evenEmptyPattern () =
        let ttaTraverser = TtaTransform.ToTTATraverser(1)
        let pred = predicate "isEven" [nat]
        let xs = [Z]
        let automaton = ttaTraverser.GetOrAddApplicationAutomaton pred xs
        let decls = List.map toString automaton.Declarations
        ()

    [<Test>]
    member x.evenSSPattern () =
        let ttaTraverser = TtaTransform.ToTTATraverser(1)
        let pred = predicate "isEven" [nat]
        let xs = [S (S nNat)]
        let automaton = ttaTraverser.GetOrAddApplicationAutomaton pred xs
        let decls = List.map toString automaton.Declarations
        ()

    [<Test>]
    member x.ltZSPattern () =
        let ttaTraverser = TtaTransform.ToTTATraverser(1)
        let pred = predicate "lt" [nat; nat]
        let xs = [Z; S nNat]
        let automaton = ttaTraverser.GetOrAddApplicationAutomaton pred xs
        let decls = List.map toString automaton.Declarations
        ()

    [<Test>]
    member x.patternDelayNode () =
        let ttaTraverser = TtaTransform.ToTTATraverser(2)
        let pred = predicate "ltlefttree" [tree; tree]
        let xs = [xTree; node yTree zTree]
        let automaton = ttaTraverser.GetOrAddApplicationAutomaton pred xs
        let decls = List.map toString automaton.Declarations
        ()

    [<Test>]
    member x.patternNodeNode () =
        let ttaTraverser = TtaTransform.ToTTATraverser(2)
        let pred = predicate "ltlefttree" [tree; tree]
        let xs = [node vTree wTree; node xTree yTree]
        let automaton = ttaTraverser.GetOrAddApplicationAutomaton pred xs
        let decls = List.map toString automaton.Declarations
        ()

    [<Test>]
    member x.patternLeafNode () =
        let ttaTraverser = TtaTransform.ToTTATraverser(2)
        let pred = predicate "ltlefttree" [tree; tree]
        let xs = [leaf; node xTree yTree]
        let automaton = ttaTraverser.GetOrAddApplicationAutomaton pred xs
        let decls = List.map toString automaton.Declarations
        ()

    [<Test>]
    member x.patternLeafLeaf () =
        let ttaTraverser = TtaTransform.ToTTATraverser(2)
        let pred = predicate "ltlefttree" [tree; tree]
        let xs = [leaf; leaf]
        let automaton = ttaTraverser.GetOrAddApplicationAutomaton pred xs
        let decls = List.map toString automaton.Declarations
        ()

    [<Test>]
    member x.strategiesTest1 () =
        let ttaTraverser = TtaTransform.ToTTATraverser(2)
        let pred = predicate "pred" [tree; tree]
        let patterns = [
            TtaTransform.Pattern([leaf; node xTree yTree])
            TtaTransform.Pattern([node xTree yTree; node vTree wTree])
            TtaTransform.Pattern([xTree; yTree])
        ]
        let auts = ttaTraverser.GeneratePatternAutomata true pred patterns
        ()

    [<Test>]
    member x.strategiesTest2 () =
        let ttaTraverser = TtaTransform.ToTTATraverser(2)
        let pred = predicate "pred" [tree; tree]
        let patterns = [
            TtaTransform.Pattern([xTree; yTree])
        ]
        let auts = ttaTraverser.GeneratePatternAutomata true pred patterns
        ()
        
    [<Test>]
    member x.strategiesTest3 () =
        let ttaTraverser = TtaTransform.ToTTATraverser(2)
        let pred = predicate "pred" [tree; tree]
        let patterns = [
            TtaTransform.Pattern([node xTree yTree; node vTree wTree])
        ]
        let auts = ttaTraverser.GeneratePatternAutomata true pred patterns
        ()
