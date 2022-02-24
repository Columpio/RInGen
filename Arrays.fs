module RInGen.Arrays
open RInGen.Operations
open RInGen.IdentGenerator
open Rule

module private V =
    let a = gensymp "a"
    let b = gensymp "b"
    let i = gensymp "i"
    let j = gensymp "j"
    let x = gensymp "x"
    let y = gensymp "y"

let private el3ar1ind2 arrSort indSort elSort =
    let x, y, z = Term.generateVariable elSort, Term.generateVariable elSort, Term.generateVariable elSort
    let arr1, arr2, i, j = Term.generateVariable arrSort, Term.generateVariable arrSort, Term.generateVariable indSort, Term.generateVariable indSort
    x, y, z, arr1, arr2, i, j

let private generateElementEqDeclarations newArraySort newIndexSort newElementSort select store eqElem eqIndex diseqIndex =
    let x, y, z, arr, _, i, j = el3ar1ind2 newArraySort newIndexSort newElementSort
    let symmetry = clARule [eqElem x y] (eqElem y x)
    let transitivity = clARule [eqElem x y; eqElem y z] (eqElem x z)
    let selectSame = clARule [eqIndex i j; eqElem x y] (eqElem (select (store arr i x) j) y)
    let selectDiff = clARule [diseqIndex i j] (eqElem (select (store arr j x) i) (select arr i))
    List.map TransformedCommand [symmetry; transitivity; selectSame; selectDiff]

let private generateElementDiseqDeclarations newArraySort newIndexSort newElementSort select store eqElement eqIndex diseqIndex diseqElem =
    let x, y, z, arr, _, i, j = el3ar1ind2 newArraySort newIndexSort newElementSort
    let symmetry = clARule [diseqElem x y] (diseqElem y x)
    let selectSame = clARule [eqIndex i j; diseqElem x y] (diseqElem (select (store arr i x) j) y)
    let selectDiff = clARule [diseqIndex i j; diseqElem (select arr i) y] (diseqElem (select (store arr j x) i) y)
    List.map TransformedCommand [symmetry; selectSame; selectDiff]

let private generateArrayEqDeclarations newArraySort newIndexSort select eqElem =
    let eq_name = gensymp ("eq" + Sort.sortToFlatString newArraySort)
    let op = Operation.makeElementaryRelationFromSorts eq_name [newArraySort; newArraySort]
    let eq = Atom.apply2 op
    let decl = DeclareFun(eq_name, [newArraySort; newArraySort], BoolSort)
    let a, b, i = Term.generateVariable newArraySort, Term.generateVariable newArraySort, Term.generateVariable newIndexSort
    let refl = clAFact (eq a a)
    let extensionality = aerule [a; b] [i] [eqElem (select a i) (select b i)] (eq a b)
    op, [OriginalCommand decl; TransformedCommand refl; TransformedCommand extensionality]

let generateArrayDiseqDeclarations newArraySort newIndexSort newElementSort select diseqElem =
    let diseq_name = gensymp ("diseq" + Sort.sortToFlatString newArraySort)
    let op = Operation.makeElementaryRelationFromSorts diseq_name [newArraySort; newArraySort]
    let diseq = Atom.apply2 op
    let decl = DeclareFun(diseq_name, [newArraySort; newArraySort], BoolSort)
    let x, y, _, a, b, i, _ = el3ar1ind2 newArraySort newIndexSort newElementSort
    let extensionality = clARule [diseqElem (select a i) (select b i)] (diseq a b)
    op, [OriginalCommand decl; TransformedCommand extensionality]

let generateEqsAndDiseqs eqs diseqs originalSorts arraySorts =
    let getNewSort = function
        | ArraySort _ as s -> Map.find s arraySorts |> fst3 |> FreeSort
        | s -> s
    let rec collectEqsAndDiseqs eqs diseqs = function
        | BoolSort -> ADTs.generateBoolCongruences eqs diseqs
        | ArraySort(originalIndexSort, originalElementSort) as originalSort ->
            let newIndexSort, newElementSort = getNewSort originalIndexSort, getNewSort originalElementSort
            let newArraySortName, selectOp, storeOp = Map.find originalSort arraySorts
            let newArraySort = FreeSort newArraySortName
            let select = Term.apply2 selectOp
            let store = Term.apply3 storeOp
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
            Atom.apply2 eqArrayOp, Atom.apply2 diseqArrayOp, Map.add newArraySort eqArrayOp eqs, Map.add newArraySort diseqArrayOp diseqs, newDecls
        | originalSort -> equalBySort eqs originalSort, disequalBySort diseqs originalSort, eqs, diseqs, []
    let originalSorts, (eqs, diseqs) =
        Set.toList originalSorts
        |> List.mapFold (fun (eqs, diseqs) sort -> let _, _, eqs, diseqs, decls = collectEqsAndDiseqs eqs diseqs sort in decls, (eqs, diseqs)) (eqs, diseqs)
    List.concat originalSorts, eqs, diseqs
