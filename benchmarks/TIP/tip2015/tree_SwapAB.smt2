(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  Tree
  ((Node (proj1-Node Tree) (proj2-Node Int) (proj3-Node Tree))
   (Nil)))
(define-fun-rec
  swap
  ((x Int) (y Int) (z Tree)) Tree
  (match z
    (((Node p x2 q)
      (ite
        (= x2 x) (Node (swap x y p) y (swap x y q))
        (ite
          (= x2 y) (Node (swap x y p) x (swap x y q))
          (Node (swap x y p) x2 (swap x y q)))))
     (Nil Nil))))
(define-fun-rec
  elem
  ((x Int) (y list)) Bool
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
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
(assert
  (not
    (forall ((p Tree) (a Int) (b Int))
      (=> (elem a (flatten0 p))
        (=> (elem b (flatten0 p))
          (and (elem a (flatten0 (swap a b p)))
            (elem b (flatten0 (swap a b p)))))))))
(check-sat)
