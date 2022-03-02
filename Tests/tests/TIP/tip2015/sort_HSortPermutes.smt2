(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype
  Heap
  ((Node (proj1-Node Heap) (proj2-Node Int) (proj3-Node Heap))
   (Nil)))
(declare-datatype list ((nil) (cons (head Heap) (tail list))))
(declare-fun lam (Int) fun12)
(declare-const lam2 fun1)
(declare-fun apply1 (fun1 Int) fun12)
(declare-fun apply12 (fun12 Int) Bool)
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
  elem
  ((x Int) (y list2)) Bool
  (match y
    ((nil2 false)
     ((cons2 z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  deleteBy
  ((x fun1) (y Int) (z list2)) list2
  (match z
    ((nil2 nil2)
     ((cons2 y2 ys)
      (ite (apply12 (apply1 x y) y2) ys (cons2 y2 (deleteBy x y ys)))))))
(define-fun-rec
  isPermutation
  ((x list2) (y list2)) Bool
  (match x
    ((nil2
      (match y
        ((nil2 true)
         ((cons2 z x2) false))))
     ((cons2 x3 xs)
      (and (elem x3 y) (isPermutation xs (deleteBy lam2 x3 y)))))))
(assert (forall ((x4 Int)) (= (apply1 lam2 x4) (lam x4))))
(assert
  (forall ((x4 Int) (x5 Int)) (= (apply12 (lam x4) x5) (= x4 x5))))
(assert (not (forall ((xs list2)) (isPermutation (hsort xs) xs))))
(check-sat)
