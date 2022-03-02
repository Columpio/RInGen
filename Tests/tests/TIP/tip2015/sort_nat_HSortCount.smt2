(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-datatype
  Heap
  ((Node (proj1-Node Heap) (proj2-Node Nat) (proj3-Node Heap))
   (Nil)))
(declare-datatype
  list2 ((nil2) (cons2 (head2 Heap) (tail2 list2))))
(define-fun-rec
  toHeap
  ((x list)) list2
  (match x
    ((nil nil2)
     ((cons y z) (cons2 (Node Nil y Nil) (toHeap z))))))
(define-fun-rec
  plus
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero y)
     ((succ z) (succ (plus z y))))))
(define-fun-rec
  leq
  ((x Nat) (y Nat)) Bool
  (match x
    ((zero true)
     ((succ z)
      (match y
        ((zero false)
         ((succ x2) (leq z x2))))))))
(define-fun-rec
  hmerge
  ((x Heap) (y Heap)) Heap
  (match x
    (((Node z x2 x3)
      (match y
        (((Node x4 x5 x6)
          (ite
            (leq x2 x5) (Node (hmerge x3 (Node x4 x5 x6)) x2 z)
            (Node (hmerge (Node z x2 x3) x6) x5 x4)))
         (Nil (Node z x2 x3)))))
     (Nil y))))
(define-fun-rec
  hpairwise
  ((x list2)) list2
  (match x
    ((nil2 nil2)
     ((cons2 q y)
      (match y
        ((nil2 (cons2 q nil2))
         ((cons2 r qs) (cons2 (hmerge q r) (hpairwise qs)))))))))
(define-fun-rec
  hmerging
  ((x list2)) Heap
  (match x
    ((nil2 Nil)
     ((cons2 q y)
      (match y
        ((nil2 q)
         ((cons2 z x2) (hmerging (hpairwise (cons2 q (cons2 z x2)))))))))))
(define-fun
  toHeap2
  ((x list)) Heap (hmerging (toHeap x)))
(define-fun-rec
  toList
  ((x Heap)) list
  (match x
    (((Node q y r) (cons y (toList (hmerge q r))))
     (Nil nil))))
(define-fun
  hsort
  ((x list)) list (toList (toHeap2 x)))
(define-fun-rec
  count
  ((x Nat) (y list)) Nat
  (match y
    ((nil zero)
     ((cons z ys)
      (ite (= x z) (plus (succ zero) (count x ys)) (count x ys))))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert
  (not
    (forall ((x Nat) (xs list))
      (= (count x (hsort xs)) (count x xs)))))
(check-sat)
