(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun-rec
  even
  ((x Nat)) Bool
  (match x
    ((Z true)
     ((S y)
      (match y
        ((Z false)
         ((S z) (even z))))))))
(define-fun-rec
  +2
  ((x Nat) (y Nat)) Nat
  (match x
    ((Z y)
     ((S z) (S (+2 z y))))))
(assert
  (not
    (forall ((x Nat) (y Nat)) (= (even (+2 x y)) (even (+2 y x))))))
(check-sat)
