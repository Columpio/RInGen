(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun-rec
  half
  ((x Nat)) Nat
  (match x
    ((Z Z)
     ((S y)
      (match y
        ((Z Z)
         ((S z) (S (half z)))))))))
(define-fun-rec
  +2
  ((x Nat) (y Nat)) Nat
  (match x
    ((Z y)
     ((S z) (S (+2 z y))))))
(assert
  (not
    (forall ((x Nat) (y Nat)) (= (half (+2 x y)) (half (+2 y x))))))
(check-sat)
