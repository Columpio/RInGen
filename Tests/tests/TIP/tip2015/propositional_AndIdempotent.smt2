(declare-datatype
  pair ((pair2 (proj1-pair Int) (proj2-pair Bool))))
(declare-datatype
  list3 ((nil3) (cons3 (head3 Bool) (tail3 list3))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(declare-datatype
  list2 ((nil2) (cons2 (head2 list) (tail2 list2))))
(declare-datatype
  Form
  ((|:&:| (|proj1-:&:| Form) (|proj2-:&:| Form))
   (Not (proj1-Not Form)) (Var (proj1-Var Int))))
(define-fun-rec
  or2
  ((x list3)) Bool
  (match x
    ((nil3 false)
     ((cons3 y xs) (or y (or2 xs))))))
(define-fun-rec
  models7
  ((x Int) (y list)) list
  (match y
    ((nil nil)
     ((cons z xs)
      (ite
        (distinct x (match z (((pair2 x2 y2) x2)))) (cons z (models7 x xs))
        (models7 x xs))))))
(define-fun-rec
  models6
  ((x Int) (y list)) list3
  (match y
    ((nil nil3)
     ((cons z x2)
      (match z
        (((pair2 y2 x3)
          (ite x3 (models6 x x2) (cons3 (= x y2) (models6 x x2))))))))))
(define-fun-rec
  models4
  ((x Int) (y list)) list3
  (match y
    ((nil nil3)
     ((cons z x2)
      (match z
        (((pair2 y2 x3)
          (ite x3 (cons3 (= x y2) (models4 x x2)) (models4 x x2)))))))))
(define-fun-rec
  ++
  ((x list2) (y list2)) list2
  (match x
    ((nil2 y)
     ((cons2 z xs) (cons2 z (++ xs y))))))
(define-funs-rec
  ((models3
    ((x Form) (y list)) list2)
   (models2
    ((q Form) (x list2)) list2)
   (models
    ((x list2) (q Form) (y list2)) list2))
  ((match x
     (((|:&:| p q) (models2 q (models3 p y)))
      ((Not z)
       (match z
         (((|:&:| r q2)
           (++ (models3 (Not r) y) (models3 (|:&:| r (Not q2)) y)))
          ((Not p2) (models3 p2 y))
          ((Var x2)
           (ite
             (not (or2 (models4 x2 y)))
             (cons2 (cons (pair2 x2 false) (models7 x2 y)) nil2) nil2)))))
      ((Var x3)
       (ite
         (not (or2 (models6 x3 y)))
         (cons2 (cons (pair2 x3 true) (models7 x3 y)) nil2) nil2))))
   (match x
     ((nil2 nil2)
      ((cons2 y z) (models z q (models3 q y)))))
   (match y
     ((nil2 (models2 q x))
      ((cons2 z x2) (cons2 z (models x q x2)))))))
(define-fun
  valid
  ((x Form)) Bool
  (match (models3 (Not x) nil)
    ((nil2 true)
     ((cons2 y z) false))))
(assert
  (not (forall ((p Form)) (= (valid (|:&:| p p)) (valid p)))))
(check-sat)
