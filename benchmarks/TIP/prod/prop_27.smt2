(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(define-fun-rec
  qrev
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (qrev xs (cons z y))))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  rev
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y xs) (++ (rev xs) (cons y nil))))))
(assert (not (forall ((x list)) (= (rev x) (qrev x nil)))))
(check-sat)
