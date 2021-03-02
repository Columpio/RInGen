(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(define-fun-rec
  butlast
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y z)
      (match z
        ((nil nil)
         ((cons x2 x3) (cons y (butlast (cons x2 x3))))))))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(assert
  (not
    (forall ((xs list) (x sk)) (= (butlast (++ xs (cons x nil))) xs))))
(check-sat)
