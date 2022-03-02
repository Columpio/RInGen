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
(define-fun
  butlastConcat
  ((x list) (y list)) list
  (match y
    ((nil (butlast x))
     ((cons z x2) (++ x (butlast (cons z x2)))))))
(assert
  (not
    (forall ((xs list) (ys list))
      (= (butlast (++ xs ys)) (butlastConcat xs ys)))))
(check-sat)
