(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun-rec
  max
  ((x Nat) (y Nat)) Nat
  (match x
    ((Z y)
     ((S z)
      (match y
        ((Z (S z))
         ((S x2) (S (max z x2)))))))))
(assert
  (not
    (forall ((a Nat) (b Nat) (c Nat))
      (= (max (max a b) c) (max a (max b c))))))
(check-sat)
