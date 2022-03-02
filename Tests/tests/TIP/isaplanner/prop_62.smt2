(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(define-fun-rec
  last
  ((x list)) Nat
  (match x
    ((nil Z)
     ((cons y z)
      (match z
        ((nil y)
         ((cons x2 x3) (last (cons x2 x3)))))))))
(assert
  (not
    (forall ((xs list) (x Nat))
      (=>
        (not
          (match xs
            ((nil true)
             ((cons y z) false))))
        (= (last (cons x xs)) (last xs))))))
(check-sat)
