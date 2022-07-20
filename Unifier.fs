module RInGen.Unifier
open SMTLIB2

type private unifier = Map<sorted_var, term>
type private unificationStatus = UnificationSuccess of unifier | UnificationFailure | UnificationUnknown of term * term



let private unifyTermsWith isConstructor preferredSet unpreferredSet =
    // invariant:   `unifier` maps x |-> t, such that domain(unifier) ∩ FV(range(unifier)) = ∅
    //              so `substInTerm unifier` returns term `t` with FV(t) ∩ domain(unifier) = ∅
    let rec occursIn v s = function
        | TConst _ -> false
        | TIdent(v2, s2) -> v = v2 && s = s2
        | TApply(_, ts) -> List.exists (occursIn v s) ts
    let addToUnifier unifier v t =
        // invariant:   ({v} ∪ FV(t)) ∩ domain(unifier) = ∅ and {v} ∩ FV(t) = ∅
        // unifier' = unifier ∪ [v |-> t]
        // domain(unifier') ∩ FV(range(unifier')) = (domain(unifier) ∪ {v}) ∩ (FV(range(unifier)) ∪ FV(t)) = {v} ∩ FV(range(unifier))
        if Set.contains v unpreferredSet then UnificationUnknown(TIdent v, t) else
        unifier
        |> Map.map (fun _ -> Term.substituteWithPair v t)
        |> Map.add v t
        |> UnificationSuccess
    let rec unifyTermsWith unifier (t1, t2) =
        if t1 = t2 then UnificationSuccess unifier else
        let t1 = Term.substituteWith unifier t1
        let t2 = Term.substituteWith unifier t2
        if t1 = t2 then UnificationSuccess unifier else
        match t1, t2 with
        | TIdent(v1, s1), TIdent(v2, s2) ->
            let vs1 = v1, s1
            let vs2 = v2, s2
            let vs, t =
                match Set.contains vs1 preferredSet, Set.contains vs2 preferredSet with
                | true, false -> vs1, t2
                | false, true -> vs2, t1
                | _ ->
                    match Set.contains vs1 unpreferredSet, Set.contains vs2 unpreferredSet with
                    | true, _ -> vs2, t1
                    | _, true -> vs1, t2
                    | _ -> if v1 < v2 then vs2, t1 else vs1, t2
            addToUnifier unifier vs t
        | TIdent(v, s), (TApply _ as a)
        | (TApply _ as a), TIdent(v, s) ->
            if occursIn v s a then UnificationFailure else addToUnifier unifier (v, s) a
        | TIdent(v, s), (TConst _ as a)
        | (TConst _ as a), TIdent(v, s) -> addToUnifier unifier (v, s) a
        | TConst _, _ | _, TConst _ -> UnificationFailure
        | TApply(op1, ts1), TApply(op2, ts2) when isConstructor op1 && isConstructor op2 ->
            if op1 <> op2 then UnificationFailure
            else unifyTermListsWith unifier (List.zip ts1 ts2)
        | _ -> UnificationUnknown(t1, t2)
    and unifyTermListsWith unifier = function
        | [] -> UnificationSuccess unifier
        | t1t2::ts ->
            match unifyTermsWith unifier t1t2 with
            | UnificationSuccess unifier -> unifyTermListsWith unifier ts
            | _ -> UnificationFailure
    unifyTermsWith

let private unifyTermListsWith unifier preferredSet unpreferredSet isConstructor ts =
    let rec iter unifier k = function
        | [] -> k ([], Some unifier)
        | t1t2::ts ->
            match unifyTermsWith isConstructor preferredSet unpreferredSet unifier t1t2 with
            | UnificationSuccess unifier -> iter unifier k ts
            | UnificationFailure -> [], None
            | UnificationUnknown(t1, t2) -> iter unifier (fun (ts, unifier) -> k ((t1, t2)::ts, unifier)) ts
    iter unifier id ts

let fromList = unifyTermListsWith Map.empty
