(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-fun lam (Int) fun12)
(declare-const lam2 fun1)
(declare-fun lam3 (Int) fun12)
(declare-fun lam4 (Int) fun12)
(declare-fun apply1 (fun1 Int) fun12)
(declare-fun apply12 (fun12 Int) Bool)
(define-fun-rec
  filter
  ((p fun12) (x list)) list
  (match x
    ((nil nil)
     ((cons y xs)
      (ite (apply12 p y) (cons y (filter p xs)) (filter p xs))))))
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
(assert (forall ((x4 Int)) (= (apply1 lam2 x4) (lam x4))))
(assert
  (forall ((x4 Int) (x5 Int)) (= (apply12 (lam x4) x5) (= x4 x5))))
(assert
  (forall ((y Int) (z Int)) (= (apply12 (lam3 y) z) (<= z y))))
(assert
  (forall ((y Int) (x2 Int)) (= (apply12 (lam4 y) x2) (> x2 y))))
(assert (not (forall ((xs list)) (isPermutation (qsort xs) xs))))
(check-sat)
