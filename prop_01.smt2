(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun-rec
  double
  ((x Nat)) Nat
  (match x
    ((Z Z)
     ((S y) (S (S (double y)))))))
(define-fun-rec
  +2
  ((x Nat) (y Nat)) Nat
  (match x
    ((Z y)
     ((S z) (S (+2 z y))))))
(assert (not (forall ((x Nat)) (= (double x) (+2 x x)))))
(check-sat)
