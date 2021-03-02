(declare-datatype Nat ((zero) (succ (p Nat))))
(define-fun-rec
  acc_plus
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero y)
     ((succ z) (acc_plus z (succ y))))))
(define-fun-rec
  acc_alt_mul
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero zero)
     ((succ z)
      (match y
        ((zero zero)
         ((succ x2)
          (acc_plus (succ z) (acc_plus x2 (acc_alt_mul z x2))))))))))
(assert
  (not
    (forall ((x Nat) (y Nat) (z Nat))
      (= (acc_alt_mul x (acc_alt_mul y z))
        (acc_alt_mul (acc_alt_mul x y) z)))))
(check-sat)
