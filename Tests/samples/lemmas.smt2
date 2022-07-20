(set-logic HORN)
(declare-datatypes ((Nat 0)) (((Z) (S (unS Nat)))))

(declare-fun P (Nat) Bool)
(declare-fun L1 (Nat) Bool)
(declare-fun L2 (Nat) Bool)

; lemmas: (and (or (L1 x) (= x Z)) (or (L2 x) (= x (S (S Z)))))
; (and (or (L1 y) (= y Z)) (or (L2 y) (= y (S (S Z)))))

(assert (forall ((x Nat)) (=> (= x Z) (and (or (L1 x) (= x Z)) (or (L2 x) (= x (S (S Z))))))))
(assert (forall ((x Nat) (y Nat)) (=> (and (= y (S (S x))) (or (L1 x) (= x Z)) (or (L2 x) (= x (S (S Z))))) (and (or (L1 y) (= y Z)) (or (L2 y) (= y (S (S Z))))))))

(assert (forall ((x Nat)) (=> (and (= x (S Z)) (and (or (L1 x) (= x Z)) (or (L2 x) (= x (S (S Z)))))) false)))
(check-sat)
(get-model)