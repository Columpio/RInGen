module FLispy.IntToNat
open FLispy.Operations

let internal nat_sort = gensymp "Nat"
let private Z_constr = gensymp "Z"
let private S_constr = gensymp "S"
let private unS_constr = gensymp "unS"
let private S_op = Operation.makeElementaryOperationFromSorts S_constr [nat_sort] nat_sort
let private Z = Ident(Z_constr, nat_sort)
let private S t = Apply(S_op, [t])

let rec int_to_nat n = if n <= 0 then Z else S (int_to_nat (n - 1))

module private V =
    let x = gensymp "x"
    let y = gensymp "y"
    let r = gensymp "r"
    let z = gensymp "z"
    let xvar = (x, nat_sort)
    let yvar = (y, nat_sort)
    let rvar = (r, nat_sort)
    let zvar = (z, nat_sort)
    let xid = Ident xvar
    let yid = Ident yvar
    let rid = Ident rvar
    let zid = Ident zvar

let nat_datatype = DeclareDatatype(nat_sort, [Z_constr, []; S_constr, [unS_constr, nat_sort]])
let private add_name = gensymp "add"
let private add_sorts = Operation.makeOperationSortsFromTypes [nat_sort; nat_sort] nat_sort
let private add_op = ElementaryOperation(add_name, Operation.makeOperationSortsFromTypes add_sorts "Bool")
let private add_app x y r = Operation.makeApp add_op [x; y] r
let private add_decl =
    [
        DeclareFun(add_name, add_sorts, "Bool")
        Assert(Forall([V.yvar], hence [] (add_app Z V.yid V.yid)))
        Assert(Forall([V.xvar; V.yvar; V.rvar], hence [add_app V.xid V.yid V.rid] (add_app (S V.xid) V.yid (S V.rid))))
    ]
let private minus_name = gensymp "minus"
let private minus_sorts = add_sorts
let private minus_op = ElementaryOperation(minus_name, Operation.makeOperationSortsFromTypes minus_sorts "Bool")
let private minus_app x y r = Operation.makeApp minus_op [x; y] r
let private minus_decl =
    [
        DeclareFun(minus_name, minus_sorts, "Bool")
        Assert(Forall([V.yvar], hence [] (minus_app Z V.yid Z)))
        Assert(Forall([V.xvar; V.yvar; V.rvar], hence [minus_app V.xid V.yid V.rid] (minus_app (S V.xid) V.yid (S V.rid))))
    ]
let private le_name = gensymp "le"
let private le_sorts = [nat_sort; nat_sort]
let private le_op = ElementaryOperation(le_name, Operation.makeOperationSortsFromTypes le_sorts "Bool")
let private le_app x y = Apply(le_op, [x; y])
let private le_decl =
    [
        DeclareFun(le_name, le_sorts, "Bool")
        Assert(Forall([V.yvar], hence [] (le_app Z V.yid)))
        Assert(Forall([V.xvar; V.yvar], hence [le_app V.xid V.yid] (le_app (S V.xid) (S V.yid))))
    ]
let private ge_name = gensymp "ge"
let private ge_sorts = [nat_sort; nat_sort]
let private ge_op = ElementaryOperation(ge_name, Operation.makeOperationSortsFromTypes ge_sorts "Bool")
let private ge_app x y = Apply(ge_op, [x; y])
let private ge_decl =
    [
        DeclareFun(ge_name, ge_sorts, "Bool")
        Assert(Forall([V.yvar], hence [] (ge_app V.yid Z)))
        Assert(Forall([V.xvar; V.yvar], hence [ge_app V.xid V.yid] (ge_app (S V.xid) (S V.yid))))
    ]
let private lt_name = gensymp "lt"
let private lt_sorts = [nat_sort; nat_sort]
let private lt_op = ElementaryOperation(lt_name, Operation.makeOperationSortsFromTypes lt_sorts "Bool")
let private lt_app x y = Apply(lt_op, [x; y])
let private lt_decl =
    [
        DeclareFun(lt_name, lt_sorts, "Bool")
        Assert(Forall([V.yvar], hence [] (lt_app Z (S V.yid))))
        Assert(Forall([V.xvar; V.yvar], hence [lt_app V.xid V.yid] (lt_app (S V.xid) (S V.yid))))
    ]
let private gt_name = gensymp "gt"
let private gt_sorts = [nat_sort; nat_sort]
let private gt_op = ElementaryOperation(gt_name, Operation.makeOperationSortsFromTypes gt_sorts "Bool")
let private gt_app x y = Apply(gt_op, [x; y])
let private gt_decl =
    [
        DeclareFun(gt_name, gt_sorts, "Bool")
        Assert(Forall([V.yvar], hence [] (gt_app (S V.yid) Z)))
        Assert(Forall([V.xvar; V.yvar], hence [gt_app V.xid V.yid] (gt_app (S V.xid) (S V.yid))))
    ]
let private mult_name = gensymp "mult"
let private mult_sorts = Operation.makeOperationSortsFromTypes [nat_sort; nat_sort] nat_sort
let private mult_op = ElementaryOperation(mult_name, Operation.makeOperationSortsFromTypes mult_sorts "Bool")
let private mult_app x y r = Operation.makeApp mult_op [x; y] r
let private mult_decl =
    [
        DeclareFun(mult_name, mult_sorts, "Bool")
        Assert(Forall([V.yvar], hence [] (mult_app Z V.yid Z)))
        Assert(Forall([V.xvar; V.yvar; V.rvar; V.zvar], hence [mult_app V.xid V.yid V.rid; add_app V.rid V.yid V.zid] (mult_app (S V.xid) V.yid V.zid)))
    ]
let private div_name = gensymp "div"
let private div_sorts = Operation.makeOperationSortsFromTypes [nat_sort; nat_sort] nat_sort
let private div_op = ElementaryOperation(div_name, Operation.makeOperationSortsFromTypes div_sorts "Bool")
let private div_app x y r = Operation.makeApp div_op [x; y] r
let private div_decl =
    [
        DeclareFun(div_name, div_sorts, "Bool")
        Assert(Forall([V.xvar; V.yvar], hence [lt_app V.xid V.yid] (div_app V.xid V.yid Z)))
        Assert(Forall([V.xvar; V.yvar; V.rvar; V.zvar], hence [ge_app V.xid V.yid; minus_app V.xid V.yid V.zid; div_app V.zid V.yid V.rid] (div_app V.xid V.yid (S V.rid))))
    ]
let private mod_name = gensymp "mod"
let private mod_sorts = Operation.makeOperationSortsFromTypes [nat_sort; nat_sort] nat_sort
let private mod_op = ElementaryOperation(mod_name, Operation.makeOperationSortsFromTypes mod_sorts "Bool")
let private mod_app x y r = Operation.makeApp mod_op [x; y] r
let private mod_decl =
    [
        DeclareFun(mod_name, mod_sorts, "Bool")
        Assert(Forall([V.xvar; V.yvar], hence [lt_app V.xid V.yid] (mod_app V.xid V.yid V.xid)))
        Assert(Forall([V.xvar; V.yvar; V.rvar; V.zvar], hence [ge_app V.xid V.yid; minus_app V.xid V.yid V.zid; mod_app V.zid V.yid V.rid] (mod_app V.xid V.yid V.rid)))
    ]

let substitutions = Map.ofList [
    "+", (add_op, true)
    "-", (minus_op, true)
    "*", (mult_op, true)
    "div", (div_op, true)
    "mod", (mod_op, true)
    "<=", (le_op, false)
    ">=", (ge_op, false)
    "<", (gt_op, false)
    ">", (lt_op, false)
]
let declarations = nat_datatype :: add_decl @ minus_decl @ le_decl @ ge_decl @ lt_decl @ gt_decl @ mult_decl @ div_decl @ mod_decl