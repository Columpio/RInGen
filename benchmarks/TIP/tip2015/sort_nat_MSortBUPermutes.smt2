(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list2 ((nil2) (cons2 (head2 Nat) (tail2 list2))))
(declare-datatype list ((nil) (cons (head list2) (tail list))))
(declare-const lam fun1)
(declare-fun lam2 (Nat) fun13)
(declare-const lam3 fun12)
(declare-fun apply1 (fun1 Nat) list2)
(declare-fun apply12 (fun12 Nat) fun13)
(declare-fun apply13 (fun13 Nat) Bool)
(define-fun-rec
  map2
  ((f fun1) (x list2)) list
  (match x
    ((nil2 nil)
     ((cons2 y xs) (cons (apply1 f y) (map2 f xs))))))
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
  lmerge
  ((x list2) (y list2)) list2
  (match x
    ((nil2 y)
     ((cons2 z x2)
      (match y
        ((nil2 (cons2 z x2))
         ((cons2 x3 x4)
          (ite
            (leq z x3) (cons2 z (lmerge x2 (cons2 x3 x4)))
            (cons2 x3 (lmerge (cons2 z x2) x4))))))))))
(define-fun-rec
  pairwise
  ((x list)) list
  (match x
    ((nil nil)
     ((cons xs y)
      (match y
        ((nil (cons xs nil))
         ((cons ys xss) (cons (lmerge xs ys) (pairwise xss)))))))))
(define-fun-rec
  mergingbu
  ((x list)) list2
  (match x
    ((nil nil2)
     ((cons xs y)
      (match y
        ((nil xs)
         ((cons z x2) (mergingbu (pairwise (cons xs (cons z x2)))))))))))
(define-fun
  msortbu
  ((x list2)) list2 (mergingbu (map2 lam x)))
(define-fun-rec
  elem
  ((x Nat) (y list2)) Bool
  (match y
    ((nil2 false)
     ((cons2 z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  deleteBy
  ((x fun12) (y Nat) (z list2)) list2
  (match z
    ((nil2 nil2)
     ((cons2 y2 ys)
      (ite
        (apply13 (apply12 x y) y2) ys (cons2 y2 (deleteBy x y ys)))))))
(define-fun-rec
  isPermutation
  ((x list2) (y list2)) Bool
  (match x
    ((nil2
      (match y
        ((nil2 true)
         ((cons2 z x2) false))))
     ((cons2 x3 xs)
      (and (elem x3 y) (isPermutation xs (deleteBy lam3 x3 y)))))))
(assert (forall ((y Nat)) (= (apply1 lam y) (cons2 y nil2))))
(assert (forall ((x4 Nat)) (= (apply12 lam3 x4) (lam2 x4))))
(assert
  (forall ((x4 Nat) (x5 Nat)) (= (apply13 (lam2 x4) x5) (= x4 x5))))
(assert
  (not (forall ((xs list2)) (isPermutation (msortbu xs) xs))))
(check-sat)
