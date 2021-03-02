(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun-rec
  |-2|
  ((x Nat) (y Nat)) Nat
  (match x
    ((Z Z)
     ((S z)
      (match y
        ((Z (S z))
         ((S x2) (|-2| z x2))))))))
(assert
  (not
    (forall ((m Nat) (n Nat) (k Nat))
      (= (|-2| (|-2| (S m) n) (S k)) (|-2| (|-2| m n) k)))))
(check-sat)
