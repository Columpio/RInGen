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
    (forall ((x Nat) (xs list))
      (=> (= xs nil) (= (last (cons x xs)) x)))))
(check-sat)
