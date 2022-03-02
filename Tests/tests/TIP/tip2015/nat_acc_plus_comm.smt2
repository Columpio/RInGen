(declare-datatype Nat ((zero) (succ (p Nat))))
(define-fun-rec
  acc_plus
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero y)
     ((succ z) (acc_plus z (succ y))))))
(assert
  (not (forall ((x Nat) (y Nat)) (= (acc_plus x y) (acc_plus y x)))))
(check-sat)
