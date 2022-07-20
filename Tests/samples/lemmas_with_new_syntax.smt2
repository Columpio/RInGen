(set-logic HORN)
(declare-datatypes ((Nat 0)) (((Z) (S (unS Nat)))))

(declare-fun P (Nat) Bool)

(lemma P ((x Nat)) (= x Z))
(lemma P ((y Nat)) (= y (S (S Z))))

(assert (forall ((x Nat)) (=> (= x Z) (P x))))
(assert (forall ((x Nat)) (=> (P x) (P (S (S x))))))

(assert (forall ((x Nat)) (=> (and (P x) (= x (S Z))) false)))
(check-sat)
(get-model)