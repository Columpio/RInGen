(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun-rec
  min
  ((x Nat) (y Nat)) Nat
  (match x
    ((Z Z)
     ((S z)
      (match y
        ((Z Z)
         ((S y1) (S (min z y1)))))))))
(assert
  (not
    (forall ((a Nat) (b Nat) (c Nat))
      (= (min (min a b) c) (min a (min b c))))))
(check-sat)
