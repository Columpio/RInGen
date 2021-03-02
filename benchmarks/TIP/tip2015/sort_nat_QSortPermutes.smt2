(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun lam (Nat) fun12)
(declare-const lam2 fun1)
(declare-fun lam3 (Nat) fun12)
(declare-fun lam4 (Nat) fun12)
(declare-fun apply1 (fun1 Nat) fun12)
(declare-fun apply12 (fun12 Nat) Bool)
(define-fun-rec
  lt
  ((x Nat) (y Nat)) Bool
  (match y
    ((zero false)
     ((succ z)
      (match x
        ((zero true)
         ((succ n) (lt n z))))))))
(define-fun-rec
  leq
  ((x Nat) (y Nat)) Bool
  (match x
    ((zero true)
     ((succ z)
      (match y
        ((zero false)
         ((succ x2) (leq z x2))))))))
(define-fun
  gt
  ((x Nat) (y Nat)) Bool (lt y x))
(define-fun-rec
  filter
  ((q fun12) (x list)) list
  (match x
    ((nil nil)
     ((cons y xs)
      (ite (apply12 q y) (cons y (filter q xs)) (filter q xs))))))
(define-fun-rec
  elem
  ((x Nat) (y list)) Bool
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  deleteBy
  ((x fun1) (y Nat) (z list)) list
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
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  qsort
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y xs)
      (++ (qsort (filter (lam3 y) xs))
        (++ (cons y nil) (qsort (filter (lam4 y) xs))))))))
(assert (forall ((x4 Nat)) (= (apply1 lam2 x4) (lam x4))))
(assert
  (forall ((x4 Nat) (x5 Nat)) (= (apply12 (lam x4) x5) (= x4 x5))))
(assert
  (forall ((y Nat) (z Nat)) (= (apply12 (lam3 y) z) (leq z y))))
(assert
  (forall ((y Nat) (x2 Nat)) (= (apply12 (lam4 y) x2) (gt x2 y))))
(assert (not (forall ((xs list)) (isPermutation (qsort xs) xs))))
(check-sat)
