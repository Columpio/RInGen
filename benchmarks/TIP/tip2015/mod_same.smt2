(declare-datatype Nat ((zero) (succ (p Nat))))
(define-fun-rec
  minus
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero zero)
     ((succ z)
      (match y
        ((zero zero)
         ((succ y2) (minus z y2))))))))
(define-fun-rec
  lt
  ((x Nat) (y Nat)) Bool
  (match y
    ((zero false)
     ((succ z)
      (match x
        ((zero true)
         ((succ n) (lt n z))))))))
(define-fun-rec
  mod2
  ((x Nat) (y Nat)) Nat
  (match y
    ((zero zero)
     ((succ z)
      (ite (lt x (succ z)) x (mod2 (minus x (succ z)) (succ z)))))))
(define-fun-rec
  go
  ((x Nat) (y Nat) (z Nat)) Nat
  (match z
    ((zero zero)
     ((succ x2)
      (match x
        ((zero
          (match y
            ((zero zero)
             ((succ x5) (minus (succ x2) (succ x5))))))
         ((succ x3)
          (match y
            ((zero (go x3 x2 (succ x2)))
             ((succ x4) (go x3 x4 (succ x2))))))))))))
(define-fun
  mod_structural
  ((x Nat) (y Nat)) Nat (go x zero y))
(assert
  (not
    (forall ((m Nat) (n Nat)) (= (mod2 m n) (mod_structural m n)))))
(check-sat)
