(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype
  Tree
  ((Node (proj1-Node Tree) (proj2-Node sk) (proj3-Node Tree)) (Nil)))
(declare-datatype list ((nil) (cons (head Tree) (tail list))))
(define-fun-rec
  flatten1
  ((x list)) list2
  (match x
    ((nil nil2)
     ((cons y ps)
      (match y
        (((Node z x2 q)
          (match z
            (((Node x3 x4 x5)
              (flatten1 (cons (Node x3 x4 x5) (cons (Node Nil x2 q) ps))))
             (Nil (cons2 x2 (flatten1 (cons q ps)))))))
         (Nil (flatten1 ps))))))))
(define-fun-rec
  ++
  ((x list2) (y list2)) list2
  (match x
    ((nil2 y)
     ((cons2 z xs) (cons2 z (++ xs y))))))
(define-fun-rec
  flatten0
  ((x Tree)) list2
  (match x
    (((Node p y q) (++ (flatten0 p) (++ (cons2 y nil2) (flatten0 q))))
     (Nil nil2))))
(assert
  (not (forall ((p Tree)) (= (flatten1 (cons p nil)) (flatten0 p)))))
(check-sat)
