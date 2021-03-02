(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype
  Heap
  ((Node (proj1-Node Heap) (proj2-Node Int) (proj3-Node Heap))
   (Nil)))
(declare-datatype list ((nil) (cons (head Heap) (tail list))))
(define-fun-rec
  toHeap
  ((x list2)) list
  (match x
    ((nil2 nil)
     ((cons2 y z) (cons (Node Nil y Nil) (toHeap z))))))
(define-fun-rec
  hmerge
  ((x Heap) (y Heap)) Heap
  (match x
    (((Node z x2 x3)
      (match y
        (((Node x4 x5 x6)
          (ite
            (<= x2 x5) (Node (hmerge x3 (Node x4 x5 x6)) x2 z)
            (Node (hmerge (Node z x2 x3) x6) x5 x4)))
         (Nil (Node z x2 x3)))))
     (Nil y))))
(define-fun-rec
  hpairwise
  ((x list)) list
  (match x
    ((nil nil)
     ((cons p y)
      (match y
        ((nil (cons p nil))
         ((cons q qs) (cons (hmerge p q) (hpairwise qs)))))))))
(define-fun-rec
  hmerging
  ((x list)) Heap
  (match x
    ((nil Nil)
     ((cons p y)
      (match y
        ((nil p)
         ((cons z x2) (hmerging (hpairwise (cons p (cons z x2)))))))))))
(define-fun
  toHeap2
  ((x list2)) Heap (hmerging (toHeap x)))
(define-fun-rec
  toList
  ((x Heap)) list2
  (match x
    (((Node p y q) (cons2 y (toList (hmerge p q))))
     (Nil nil2))))
(define-fun
  hsort
  ((x list2)) list2 (toList (toHeap2 x)))
(define-fun-rec
  count
  ((x Int) (y list2)) Int
  (match y
    ((nil2 0)
     ((cons2 z ys) (ite (= x z) (+ 1 (count x ys)) (count x ys))))))
(assert
  (not
    (forall ((x Int) (xs list2))
      (= (count x (hsort xs)) (count x xs)))))
(check-sat)
