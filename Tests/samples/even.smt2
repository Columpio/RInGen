; Diverge:              Spacer, Eldarica, Vampire
; Halts with invariant: RInGen
(set-logic HORN)
(declare-datatypes ((Nat 0)) (((Z) (S (unS Nat)))))

(declare-fun even (Nat) Bool)
(assert (forall ((x Nat)) (=> (= x Z) (even x))))
(assert (forall ((x Nat)) (=> (even x) (even (S (S x))))))

(assert (forall ((x Nat)) (=> (and (even x) (even (S x))) false)))
(check-sat)
(get-model)
