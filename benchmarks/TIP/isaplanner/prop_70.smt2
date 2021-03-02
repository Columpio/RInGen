(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun-rec
  <=2
  ((x Nat) (y Nat)) Bool
  (match x
    ((Z true)
     ((S z)
      (match y
        ((Z false)
         ((S x2) (<=2 z x2))))))))
(assert
  (not (forall ((m Nat) (n Nat)) (=> (<=2 m n) (<=2 m (S n))))))
(check-sat)
