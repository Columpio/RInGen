(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun-rec
  +2
  ((x Nat) (y Nat)) Nat
  (match x
    ((Z y)
     ((S z) (S (+2 z y))))))
(define-fun-rec
  mult
  ((x Nat) (y Nat) (z Nat)) Nat
  (match x
    ((Z z)
     ((S x2) (mult x2 y (+2 y z))))))
(define-fun-rec
  *2
  ((x Nat) (y Nat)) Nat
  (match x
    ((Z Z)
     ((S z) (+2 y (*2 z y))))))
(assert (not (forall ((x Nat) (y Nat)) (= (*2 x y) (mult x y Z)))))
(check-sat)
