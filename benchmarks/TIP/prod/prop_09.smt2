(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun-rec
  drop
  ((x Nat) (y list)) list
  (match x
    ((Z y)
     ((S z)
      (match y
        ((nil nil)
         ((cons x2 x3) (drop z x3))))))))
(assert
  (not
    (forall ((x Nat) (y Nat) (z list) (w Nat))
      (= (drop w (drop x (drop y z))) (drop y (drop x (drop w z)))))))
(check-sat)
