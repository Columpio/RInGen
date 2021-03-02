(declare-datatype Nat ((zero) (succ (p Nat))))
(define-fun-rec
  acc_plus
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero y)
     ((succ z) (acc_plus z (succ y))))))
(assert
  (not
    (forall ((x Nat) (y Nat) (z Nat))
      (= (acc_plus x (acc_plus y z)) (acc_plus (acc_plus x y) z)))))
(check-sat)
