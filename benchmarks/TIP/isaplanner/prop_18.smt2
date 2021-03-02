(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun-rec
  <2
  ((x Nat) (y Nat)) Bool
  (match y
    ((Z false)
     ((S z)
      (match x
        ((Z true)
         ((S x2) (<2 x2 z))))))))
(define-fun-rec
  +2
  ((x Nat) (y Nat)) Nat
  (match x
    ((Z y)
     ((S z) (S (+2 z y))))))
(assert (not (forall ((i Nat) (m Nat)) (<2 i (S (+2 i m))))))
(check-sat)
