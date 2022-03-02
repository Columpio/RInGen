(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype list ((nil) (cons (head list2) (tail list))))
(define-fun-rec
  ++
  ((x list2) (y list2)) list2
  (match x
    ((nil2 y)
     ((cons2 z xs) (cons2 z (++ xs y))))))
(define-fun-rec
  rev
  ((x list2)) list2
  (match x
    ((nil2 nil2)
     ((cons2 y xs) (++ (rev xs) (cons2 y nil2))))))
(define-fun-rec
  qrevflat
  ((x list) (y list2)) list2
  (match x
    ((nil y)
     ((cons xs xss) (qrevflat xss (++ (rev xs) y))))))
(define-fun-rec
  revflat
  ((x list)) list2
  (match x
    ((nil nil2)
     ((cons xs xss) (++ (revflat xss) (rev xs))))))
(assert
  (not (forall ((x list)) (= (revflat x) (qrevflat x nil2)))))
(check-sat)
