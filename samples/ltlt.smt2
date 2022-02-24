(set-logic HORN)

(declare-datatypes ((Nat 0)) (((Z) (S (prev Nat)))))

(declare-fun lt (Nat Nat) Bool)
(assert (forall ((y Nat)) (lt Z (S y))))
(assert (forall ((x Nat) (y Nat)) (=> (lt x y) (lt (S x) (S y)))))

(assert (forall ((x Nat) (y Nat)) (=> (and (lt x y) (lt y x)) false)))

(check-sat)
(get-model)
