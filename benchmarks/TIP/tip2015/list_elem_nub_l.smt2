(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun lam (fun12 sk) fun13)
(declare-fun lam2 (sk) fun13)
(declare-const lam3 fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) fun13)
(declare-fun apply13 (fun13 sk) Bool)
(define-fun-rec
  filter
  ((p fun13) (x list)) list
  (match x
    ((nil nil)
     ((cons y xs)
      (ite (apply13 p y) (cons y (filter p xs)) (filter p xs))))))
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
(assert
  (forall ((x fun12) (z sk) (y2 sk))
    (= (apply13 (lam x z) y2) (not (apply13 (apply12 x z) y2)))))
(assert (forall ((y sk)) (= (apply12 lam3 y) (lam2 y))))
(assert (forall ((y sk) (z sk)) (= (apply13 (lam2 y) z) (= y z))))
(assert
  (not
    (forall ((x sk) (xs list))
      (=> (elem x xs) (elem x (nubBy lam3 xs))))))
(check-sat)
