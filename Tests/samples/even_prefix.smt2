(set-logic HORN)
(declare-datatypes ((PNat 0)) (((Eps) (Z) (S (prev PNat)))))

(declare-fun evenPr (PNat) Bool)
(assert (evenPr Eps))
(assert (evenPr Z))
(assert (evenPr (S Eps)))
(assert (forall ((x PNat)) (=> (evenPr x) (evenPr (S (S x))))))

(declare-fun oddPr (PNat) Bool)
(assert (oddPr Eps))
(assert (oddPr (S Eps)))
(assert (oddPr (S Z)))
(assert (forall ((x PNat)) (=> (oddPr x) (oddPr (S (S x))))))

(assert (forall ((x PNat)) (=> (and (evenPr x) (oddPr x)) false)))
(check-sat)
(get-model)
