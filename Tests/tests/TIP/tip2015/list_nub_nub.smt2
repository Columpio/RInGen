(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun lam (fun12 sk) fun13)
(declare-fun lam2 (sk) fun13)
(declare-const lam3 fun12)
(declare-fun lam4 (sk) fun13)
(declare-const lam5 fun12)
(declare-fun lam6 (sk) fun13)
(declare-const lam7 fun12)
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
(assert
  (forall ((x fun12) (z sk) (y2 sk))
    (= (apply13 (lam x z) y2) (not (apply13 (apply12 x z) y2)))))
(assert (forall ((x sk)) (= (apply12 lam3 x) (lam2 x))))
(assert (forall ((x sk) (y sk)) (= (apply13 (lam2 x) y) (= x y))))
(assert (forall ((z sk)) (= (apply12 lam5 z) (lam4 z))))
(assert
  (forall ((z sk) (x2 sk)) (= (apply13 (lam4 z) x2) (= z x2))))
(assert (forall ((x3 sk)) (= (apply12 lam7 x3) (lam6 x3))))
(assert
  (forall ((x3 sk) (x4 sk)) (= (apply13 (lam6 x3) x4) (= x3 x4))))
(assert
  (not
    (forall ((xs list))
      (= (nubBy lam3 (nubBy lam5 xs)) (nubBy lam7 xs)))))
(check-sat)
