(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-const undefined sk)
(define-fun-rec
  elem
  ((x sk) (y list)) Bool
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  at
  ((x list) (y Nat)) sk
  (match x
    ((nil undefined)
     ((cons z x2)
      (match y
        ((zero z)
         ((succ x3) (at x2 x3))))))))
(assert
  (not
    (forall ((x sk) (xs list))
      (=> (elem x xs) (exists ((y Nat)) (= x (at xs y)))))))
(check-sat)
