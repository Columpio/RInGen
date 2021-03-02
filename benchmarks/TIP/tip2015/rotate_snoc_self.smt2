(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(define-fun-rec
  snoc
  ((x sk) (y list)) list
  (match y
    ((nil (cons x nil))
     ((cons z ys) (cons z (snoc x ys))))))
(define-fun-rec
  rotate
  ((x Nat) (y list)) list
  (match x
    ((zero y)
     ((succ z)
      (match y
        ((nil nil)
         ((cons z2 xs1) (rotate z (snoc z2 xs1)))))))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(assert
  (not
    (forall ((n Nat) (xs list))
      (= (rotate n (++ xs xs)) (++ (rotate n xs) (rotate n xs))))))
(check-sat)
