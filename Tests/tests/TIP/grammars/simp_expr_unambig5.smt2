(declare-datatype Tok ((C) (D) (X) (Y) (Pl)))
(declare-datatype list ((nil) (cons (head Tok) (tail list))))
(declare-datatype T ((TX) (TY)))
(declare-datatype
  E ((Plus (proj1-Plus T) (proj2-Plus E)) (Term (proj1-Term T))))
(define-fun
  linTerm
  ((x T)) list
  (match x
    ((TX (cons X nil))
     (TY (cons Y nil)))))
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
    (((Plus a b) (++ (linTerm a) (++ (cons Pl nil) (lin b))))
     ((Term t) (linTerm t)))))
(assert
  (not (forall ((u E) (v E)) (=> (= (lin u) (lin v)) (= u v)))))
(check-sat)
