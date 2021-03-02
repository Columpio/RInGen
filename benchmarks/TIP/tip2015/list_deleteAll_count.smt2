(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun lam (sk) fun13)
(declare-const lam2 fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) fun13)
(declare-fun apply13 (fun13 sk) Bool)
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
  ((x sk) (y list)) Int
  (match y
    ((nil 0)
     ((cons z ys) (ite (= x z) (+ 1 (count x ys)) (count x ys))))))
(assert (forall ((y sk)) (= (apply12 lam2 y) (lam y))))
(assert (forall ((y sk) (z sk)) (= (apply13 (lam y) z) (= y z))))
(assert
  (not
    (forall ((x sk) (xs list))
      (=> (= (deleteAll x xs) (deleteBy lam2 x xs))
        (<= (count x xs) 1)))))
(check-sat)
