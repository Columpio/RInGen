(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  rotate
  ((x Nat) (y list)) list
  (match x
    ((zero y)
     ((succ z)
      (match y
        ((nil nil)
         ((cons z2 xs1) (rotate z (++ xs1 (cons z2 nil))))))))))
(assert
  (not
    (forall ((n Nat) (xs list))
      (= (rotate n (++ xs xs)) (++ (rotate n xs) (rotate n xs))))))
(check-sat)
