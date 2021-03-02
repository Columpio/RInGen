(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(define-fun-rec
  interleave
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (interleave y xs))))))
(define-funs-rec
  ((evens
    ((x list)) list)
   (odds
    ((x list)) list))
  ((match x
     ((nil nil)
      ((cons y xs) (cons y (odds xs)))))
   (match x
     ((nil nil)
      ((cons y xs) (evens xs))))))
(assert
  (not
    (forall ((xs list)) (= (interleave (evens xs) (odds xs)) xs))))
(check-sat)
