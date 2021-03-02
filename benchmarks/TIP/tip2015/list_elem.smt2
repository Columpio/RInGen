(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-const undefined sk)
(define-fun-rec
  elem
  ((x sk) (y list)) Bool
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  at
  ((x list) (y Int)) sk
  (match x
    ((nil undefined)
     ((cons z x2)
      (ite (= y 0) z (ite (> y 0) (at x2 (- y 1)) undefined))))))
(assert
  (not
    (forall ((x sk) (xs list))
      (=> (elem x xs) (exists ((y Int)) (= x (at xs y)))))))
(check-sat)
