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
(define-funs-rec
  ((linTerm
    ((x E)) list)
   (lin
    ((x E)) list))
  ((match x
     (((Plus y z) (++ (cons C nil) (++ (lin (Plus y z)) (cons D nil))))
      (EX (cons X nil))
      (EY (cons Y nil))))
   (match x
     (((Plus a b) (++ (linTerm a) (++ (cons Pl nil) (linTerm b))))
      (EX (cons X nil))
      (EY (cons Y nil))))))
(assert
  (not (forall ((u E) (v E)) (=> (= (lin u) (lin v)) (= u v)))))
(check-sat)
