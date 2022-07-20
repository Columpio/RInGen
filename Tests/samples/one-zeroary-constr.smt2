(set-logic HORN)
(declare-datatype C ((Z)))

(assert (forall ((x C)) (=> (distinct x Z) false)))
(check-sat)
(get-model)
