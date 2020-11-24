(set-logic HORN)
(declare-datatypes () ((C (Z))))

(assert (forall ((x C)) (=> (distinct x Z) false)))
(check-sat)
(get-model)
