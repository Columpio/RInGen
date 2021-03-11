module RInGen.Arrays
open RInGen.Operations
open RInGen.IdentGenerator

module private V =
    let a = gensyms "a"
    let b = gensyms "b"
    let i = gensyms "i"
    let j = gensyms "j"
    let x = gensyms "x"
    let y = gensyms "y"

let private generateElementEqDeclarations newArraySort newIndexSort newElementSort select store eqElem eqIndex diseqIndex =
    let xEl = gensyms "x", newElementSort
    let yEl = gensyms "y", newElementSort
    let zEl = gensyms "z", newElementSort
    let arrEl = gensyms "arr", newArraySort
    let iEl = gensyms "i", newIndexSort
    let jEl = gensyms "j", newIndexSort
    let x, y, z, arr, i, j = TIdent xEl, TIdent yEl, TIdent zEl, TIdent arrEl, TIdent iEl, TIdent jEl
    let symmetry = rule [xEl; yEl] [eqElem x y] (eqElem y x)
    let transitivity = rule [xEl; yEl; zEl] [eqElem x y; eqElem y z] (eqElem x z)
    let selectSame = rule [arrEl; iEl; jEl; xEl; yEl] [eqIndex i j; eqElem x y] (eqElem (select (store arr i x) j) y)
    let selectDiff = rule [arrEl; iEl; jEl; xEl; yEl] [diseqIndex i j] (eqElem (select (store arr j x) i) (select arr i))
    List.map TransformedCommand [symmetry; transitivity; selectSame; selectDiff]

let private generateElementDiseqDeclarations newArraySort newIndexSort newElementSort select store eqElement eqIndex diseqIndex diseqElem =
    let xEl = gensyms "x", newElementSort
    let yEl = gensyms "y", newElementSort
    let zEl = gensyms "z", newElementSort
    let arrEl = gensyms "arr", newArraySort
    let iEl = gensyms "i", newIndexSort
    let jEl = gensyms "j", newIndexSort
    let x, y, z, arr, i, j = TIdent xEl, TIdent yEl, TIdent zEl, TIdent arrEl, TIdent iEl, TIdent jEl
    let symmetry = rule [xEl; yEl] [diseqElem x y] (diseqElem y x)
    let selectSame = rule [arrEl; iEl; jEl; xEl; yEl] [eqIndex i j; diseqElem x y] (diseqElem (select (store arr i x) j) y)
    let selectDiff = rule [arrEl; iEl; jEl; xEl; yEl] [diseqIndex i j; diseqElem (select arr i) y] (diseqElem (select (store arr j x) i) y)
    List.map TransformedCommand [symmetry; selectSame; selectDiff]

let private generateArrayEqDeclarations newArraySort newIndexSort select eqElem =
    let eq_name = gensyms ("eq" + sortToFlatString newArraySort)
    let op = Operation.makeElementaryRelationFromSorts eq_name [newArraySort; newArraySort]
    let eq = applyBinaryRelation op
    let decl = DeclareFun(eq_name, [newArraySort; newArraySort], boolSort)
    let aEl = gensyms "a", newArraySort
    let bEl = gensyms "b", newArraySort
    let iEl = gensyms "i", newIndexSort
    let a, b, i = TIdent aEl, TIdent bEl, TIdent iEl
    let refl = rule [aEl] [] (eq a a)
    let extensionality = aerule [aEl; bEl] [iEl] [eqElem (select a i) (select b i)] (eq a b)
    op, [OriginalCommand decl; TransformedCommand refl; TransformedCommand extensionality]

let generateArrayDiseqDeclarations newArraySort newIndexSort newElementSort select diseqElem =
    let diseq_name = gensyms ("diseq" + sortToFlatString newArraySort)
    let op = Operation.makeElementaryRelationFromSorts diseq_name [newArraySort; newArraySort]
    let diseq = applyBinaryRelation op
    let decl = DeclareFun(diseq_name, [newArraySort; newArraySort], boolSort)
    let aEl = gensyms "a", newArraySort
    let bEl = gensyms "b", newArraySort
    let iEl = gensyms "i", newIndexSort
    let xEl = gensyms "x", newElementSort
    let yEl = gensyms "y", newElementSort
    let x, y, a, b, i = TIdent xEl, TIdent yEl, TIdent aEl, TIdent bEl, TIdent iEl
    let extensionality = rule [aEl; bEl; iEl; xEl; yEl] [diseqElem (select a i) (select b i)] (diseq a b)
    op, [OriginalCommand decl; TransformedCommand extensionality]

let generateEqsAndDiseqs eqs diseqs originalSorts arraySorts =
    let getNewSort = function
        | ArraySort _ as s -> Map.find s arraySorts |> fst3
        | PrimitiveSort _ as s -> s
        | s -> __notImplemented__()
    let rec collectEqsAndDiseqs eqs diseqs originalSort =
        match originalSort with
        | PrimitiveSort("Bool") -> ADTs.generateBoolCongruences eqs diseqs
        | PrimitiveSort _ -> equalBySort eqs originalSort, disequalBySort diseqs originalSort, eqs, diseqs, []
        | ArraySort(originalIndexSort, originalElementSort) ->
            let newIndexSort, newElementSort = getNewSort originalIndexSort, getNewSort originalElementSort
            let newArraySort, selectOp, storeOp = Map.find originalSort arraySorts
            let select a i = TApply(selectOp, [a; i])
            let store a i v = TApply(storeOp, [a; i; v])
            let eqIndex, diseqIndex, eqs, diseqs, eqElementDeclarations = collectEqsAndDiseqs eqs diseqs originalIndexSort
            let eqElement, diseqElement, eqs, diseqs, diseqElementDeclarations = collectEqsAndDiseqs eqs diseqs originalElementSort
            let eqElementNewDeclarations = generateElementEqDeclarations newArraySort newIndexSort newElementSort select store eqElement eqIndex diseqIndex
            let diseqElementNewDeclarations = generateElementDiseqDeclarations newArraySort newIndexSort newElementSort select store eqElement eqIndex diseqIndex diseqElement
            let eqArrayOp, eqArrayDeclarations = generateArrayEqDeclarations newArraySort newIndexSort select eqElement
            let diseqArrayOp, diseqArrayDeclarations = generateArrayDiseqDeclarations newArraySort newIndexSort newElementSort select diseqElement
            let newDecls =
                eqElementDeclarations @ diseqElementDeclarations
                @ eqElementNewDeclarations @ diseqElementNewDeclarations
                @ eqArrayDeclarations @ diseqArrayDeclarations
            applyBinaryRelation eqArrayOp, applyBinaryRelation diseqArrayOp, Map.add newArraySort eqArrayOp eqs, Map.add newArraySort diseqArrayOp diseqs, newDecls
        | _ -> __notImplemented__()
    let originalSorts, (eqs, diseqs) =
        Set.toList originalSorts
        |> List.mapFold (fun (eqs, diseqs) sort -> let _, _, eqs, diseqs, decls = collectEqsAndDiseqs eqs diseqs sort in decls, (eqs, diseqs)) (eqs, diseqs)
    List.concat originalSorts, eqs, diseqs
