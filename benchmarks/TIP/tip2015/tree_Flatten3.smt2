(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype
  Tree
  ((Node (proj1-Node Tree) (proj2-Node sk) (proj3-Node Tree)) (Nil)))
(define-fun-rec
  flatten3
  ((x Tree)) list
  (match x
    (((Node y z r)
      (match y
        (((Node p x2 q) (flatten3 (Node p x2 (Node q z r))))
         (Nil (cons z (flatten3 r))))))
     (Nil nil))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  flatten0
  ((x Tree)) list
  (match x
    (((Node p y q) (++ (flatten0 p) (++ (cons y nil) (flatten0 q))))
     (Nil nil))))
(assert (not (forall ((p Tree)) (= (flatten3 p) (flatten0 p)))))
(check-sat)
