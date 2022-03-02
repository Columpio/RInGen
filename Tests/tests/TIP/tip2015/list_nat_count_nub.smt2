(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun lam (fun12 sk) fun13)
(declare-fun lam2 (sk) fun13)
(declare-const lam3 fun12)
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
  filter
  ((q fun13) (x list)) list
  (match x
    ((nil nil)
     ((cons y xs)
      (ite (apply13 q y) (cons y (filter q xs)) (filter q xs))))))
(define-fun-rec
  nubBy
  ((x fun12) (y list)) list
  (match y
    ((nil nil)
     ((cons z xs) (cons z (nubBy x (filter (lam x z) xs)))))))
(define-fun-rec
  elem
  ((x sk) (y list)) Bool
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
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
(assert
  (forall ((x fun12) (z sk) (y2 sk))
    (= (apply13 (lam x z) y2) (not (apply13 (apply12 x z) y2)))))
(assert (forall ((y sk)) (= (apply12 lam3 y) (lam2 y))))
(assert (forall ((y sk) (z sk)) (= (apply13 (lam2 y) z) (= y z))))
(assert
  (not
    (forall ((x sk) (xs list))
      (=> (elem x xs) (= (count x (nubBy lam3 xs)) (succ zero))))))
(check-sat)
