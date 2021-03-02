(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun lam (Nat) fun12)
(declare-const lam2 fun1)
(declare-fun lam3 (Nat) fun12)
(declare-const lam4 fun1)
(declare-fun apply1 (fun1 Nat) fun12)
(declare-fun apply12 (fun12 Nat) Bool)
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
  ssort-minimum1
  ((x Nat) (y list)) Nat
  (match y
    ((nil x)
     ((cons y1 ys1)
      (ite (leq y1 x) (ssort-minimum1 y1 ys1) (ssort-minimum1 x ys1))))))
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
  ssort
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y ys)
      (let ((m (ssort-minimum1 y ys)))
        (cons m (ssort (deleteBy lam4 m (cons y ys)))))))))
(assert (forall ((x4 Nat)) (= (apply1 lam2 x4) (lam x4))))
(assert
  (forall ((x4 Nat) (x5 Nat)) (= (apply12 (lam x4) x5) (= x4 x5))))
(assert (forall ((z Nat)) (= (apply1 lam4 z) (lam3 z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (apply12 (lam3 z) x2) (= z x2))))
(assert (not (forall ((xs list)) (isPermutation (ssort xs) xs))))
(check-sat)
