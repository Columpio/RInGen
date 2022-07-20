module RInGen.ADTExtensions

let rec isGround = function
    | TApply(_, ts) -> List.forall isGround ts
    | _ -> false
