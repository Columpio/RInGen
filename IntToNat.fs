module RInGen.IntToNat
open RInGen.SubstituteOperations
open RInGen.Operations
open RInGen.IdentGenerator

type IntToNat () =
    inherit TheorySubstitutor ()
    let nat_sort = gensyms "Nat" |> PrimitiveSort

    let Z_constr = gensyms "Z"
    let S_constr = gensyms "S"
    let unS_constr = gensyms "unS"
    let S_op = Operation.makeElementaryOperationFromSorts S_constr [nat_sort] nat_sort
    let Z = TConst(Z_constr, nat_sort)
    let S t = TApply(S_op, [t])

    let rec int_to_natrec (n : int64) = if n <= 0L then Z else S (int_to_natrec (n - 1L))

    let x = gensyms "x"
    let y = gensyms "y"
    let r = gensyms "r"
    let z = gensyms "z"
    let xvar = (x, nat_sort)
    let yvar = (y, nat_sort)
    let rvar = (r, nat_sort)
    let zvar = (z, nat_sort)
    let xid = TIdent xvar
    let yid = TIdent yvar
    let rid = TIdent rvar
    let zid = TIdent zvar

    let nat_datatype = DeclareDatatype(nat_sort, [Z_constr, []; S_constr, [unS_constr, nat_sort]])

    let add_app, add_def, add_op = Relativization.createBinaryOperation "add" nat_sort nat_sort nat_sort
    let minus_app, minus_def, minus_op = Relativization.createBinaryOperation "minus" nat_sort nat_sort nat_sort
    let mult_app, mult_def, mult_op = Relativization.createBinaryOperation "mult" nat_sort nat_sort nat_sort
    let div_app, div_def, div_op = Relativization.createBinaryOperation "div" nat_sort nat_sort nat_sort
    let mod_app, mod_def, mod_op = Relativization.createBinaryOperation "mod" nat_sort nat_sort nat_sort
    let le_app, le_def, le_op = Relativization.createBinaryRelation "le" nat_sort nat_sort
    let ge_app, ge_def, ge_op = Relativization.createBinaryRelation "ge" nat_sort nat_sort
    let lt_app, lt_def, lt_op = Relativization.createBinaryRelation "lt" nat_sort nat_sort
    let gt_app, gt_def, gt_op = Relativization.createBinaryRelation "gt" nat_sort nat_sort
    let add_decl =
        [
            rule [yvar] [] (add_app Z yid yid)
            rule [xvar; yvar; rvar] [add_app xid yid rid] (add_app (S xid) yid (S rid))
        ]
    let minus_decl =
        [
            rule [yvar] [] (minus_app Z yid Z)
            rule [xvar; yvar; rvar] [minus_app xid yid rid] (minus_app (S xid) yid (S rid))
        ]
    let le_decl =
        [
            rule [yvar] [] (le_app Z yid)
            rule [xvar; yvar] [le_app xid yid] (le_app (S xid) (S yid))
        ]
    let ge_decl =
        [
            rule [yvar] [] (ge_app yid Z)
            rule [xvar; yvar] [ge_app xid yid] (ge_app (S xid) (S yid))
        ]
    let lt_decl =
        [
            rule [yvar] [] (lt_app Z (S yid))
            rule [xvar; yvar] [lt_app xid yid] (lt_app (S xid) (S yid))
        ]
    let gt_decl =
        [
            rule [yvar] [] (gt_app (S yid) Z)
            rule [xvar; yvar] [gt_app xid yid] (gt_app (S xid) (S yid))
        ]
    let mult_decl =
        [
            rule [yvar] [] (mult_app Z yid Z)
            rule [xvar; yvar; rvar; zvar] [mult_app xid yid rid; add_app rid yid zid] (mult_app (S xid) yid zid)
        ]
    let div_decl =
        [
            rule [xvar; yvar] [lt_app xid yid] (div_app xid yid Z)
            rule [xvar; yvar; rvar; zvar] [ge_app xid yid; minus_app xid yid zid; div_app zid yid rid] (div_app xid yid (S rid))
        ]
    let mod_decl =
        [
            rule [xvar; yvar] [lt_app xid yid] (mod_app xid yid xid)
            rule [xvar; yvar; rvar; zvar] [ge_app xid yid; minus_app xid yid zid; mod_app zid yid rid] (mod_app xid yid rid)
        ]

    let substitutions =
        [
            "+", (add_op, true)
            "-", (minus_op, true)
            "*", (mult_op, true)
            "div", (div_op, true)
            "mod", (mod_op, true)
            "<=", (le_op, false)
            ">=", (ge_op, false)
            ">", (gt_op, false)
            "<", (lt_op, false)
        ] |> List.map (fun (name, op) -> Map.find (symbol name) elementaryOperations, op) |> Map.ofList
    let preamble =
        List.map OriginalCommand [nat_datatype; add_def; minus_def; le_def; ge_def; lt_def; gt_def; mult_def; div_def; mod_def]
        @ List.map TransformedCommand (add_decl @ minus_decl @ le_decl @ ge_decl @ lt_decl @ gt_decl @ mult_decl @ div_decl @ mod_decl)

    let intConstToNat (s: symbol) =
        let r = ref 0L
        if System.Int64.TryParse(s.ToString(), r) then Some (int_to_natrec !r) else None

    override x.GenerateDeclarations() = preamble, nat_sort, substitutions, intConstToNat

    override x.TryMapSort(s) = if s = integerSort then Some nat_sort else None
