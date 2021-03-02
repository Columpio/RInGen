(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun lam (sk) fun13)
(declare-const lam2 fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) fun13)
(declare-fun apply13 (fun13 sk) Bool)
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
  deleteBy
  ((x fun12) (y sk) (z list)) list
  (match z
    ((nil nil)
     ((cons y2 ys)
      (ite (apply13 (apply12 x y) y2) ys (cons y2 (deleteBy x y ys)))))))
(define-fun-rec
  deleteAll
  ((x sk) (y list)) list
  (match y
    ((nil nil)
     ((cons z ys)
      (ite (= x z) (deleteAll x ys) (cons z (deleteAll x ys)))))))
(define-fun-rec
  count
  ((x sk) (y list)) Nat
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
(assert (forall ((y sk)) (= (apply12 lam2 y) (lam y))))
(assert (forall ((y sk) (z sk)) (= (apply13 (lam y) z) (= y z))))
(assert
  (not
    (forall ((x sk) (xs list))
      (=> (= (deleteAll x xs) (deleteBy lam2 x xs))
        (leq (count x xs) (succ zero))))))
(check-sat)
