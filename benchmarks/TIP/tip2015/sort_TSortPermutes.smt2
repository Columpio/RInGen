(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  Tree
  ((TNode (proj1-TNode Tree) (proj2-TNode Int) (proj3-TNode Tree))
   (TNil)))
(declare-fun lam (Int) fun12)
(declare-const lam2 fun1)
(declare-fun apply1 (fun1 Int) fun12)
(declare-fun apply12 (fun12 Int) Bool)
(define-fun-rec
  flatten
  ((x Tree) (y list)) list
  (match x
    (((TNode p z q) (flatten p (cons z (flatten q y))))
     (TNil y))))
(define-fun-rec
  elem
  ((x Int) (y list)) Bool
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  deleteBy
  ((x fun1) (y Int) (z list)) list
  (match z
    ((nil nil)
     ((cons y2 ys)
      (ite (apply12 (apply1 x y) y2) ys (cons y2 (deleteBy x y ys)))))))
(define-fun-rec
  isPermutation
  ((x list) (y list)) Bool
  (match x
    ((nil
      (match y
        ((nil true)
         ((cons z x2) false))))
     ((cons x3 xs)
      (and (elem x3 y) (isPermutation xs (deleteBy lam2 x3 y)))))))
(define-fun-rec
  add
  ((x Int) (y Tree)) Tree
  (match y
    (((TNode p z q)
      (ite (<= x z) (TNode (add x p) z q) (TNode p z (add x q))))
     (TNil (TNode TNil x TNil)))))
(define-fun-rec
  toTree
  ((x list)) Tree
  (match x
    ((nil TNil)
     ((cons y xs) (add y (toTree xs))))))
(define-fun
  tsort
  ((x list)) list (flatten (toTree x) nil))
(assert (forall ((x4 Int)) (= (apply1 lam2 x4) (lam x4))))
(assert
  (forall ((x4 Int) (x5 Int)) (= (apply12 (lam x4) x5) (= x4 x5))))
(assert (not (forall ((xs list)) (isPermutation (tsort xs) xs))))
(check-sat)
