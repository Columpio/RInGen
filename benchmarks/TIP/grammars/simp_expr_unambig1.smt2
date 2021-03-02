(declare-datatype Tok ((C) (D) (X) (Y) (Pl)))
(declare-datatype list ((nil) (cons (head Tok) (tail list))))
(declare-datatype
  E ((Plus (proj1-Plus E) (proj2-Plus E)) (EX) (EY)))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  lin
  ((x E)) list
  (match x
    (((Plus a b)
      (++ (cons C nil)
        (++ (lin a) (++ (cons Pl nil) (++ (lin b) (cons D nil))))))
     (EX (cons X nil))
     (EY (cons Y nil)))))
(assert
  (not (forall ((u E) (v E)) (=> (= (lin u) (lin v)) (= u v)))))
(check-sat)
