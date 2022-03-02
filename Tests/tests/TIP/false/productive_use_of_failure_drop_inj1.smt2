(declare-datatype Nat ((S (proj1-S Nat)) (Z)))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(define-fun-rec
  drop
  ((x Nat) (y list)) list
  (match x
    (((S z)
      (match y
        ((nil nil)
         ((cons x2 x3) (drop z x3)))))
     (Z y))))
(assert
  (not
    (forall ((n Nat) (m Nat) (xs list))
      (=> (= (drop n xs) (drop m xs)) (= n m)))))
(check-sat)
