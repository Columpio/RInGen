(declare-sort fun1 0)
(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-fun lam (Int) fun1)
(declare-fun lam2 (Int) fun1)
(declare-fun apply1 (fun1 Int) Bool)
(define-fun-rec
  filter
  ((p fun1) (x list)) list
  (match x
    ((nil nil)
     ((cons y xs)
      (ite (apply1 p y) (cons y (filter p xs)) (filter p xs))))))
(define-fun-rec
  count
  ((x Int) (y list)) Int
  (match y
    ((nil 0)
     ((cons z ys) (ite (= x z) (+ 1 (count x ys)) (count x ys))))))
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
      (++ (qsort (filter (lam y) xs))
        (++ (cons y nil) (qsort (filter (lam2 y) xs))))))))
(assert (forall ((y Int) (z Int)) (= (apply1 (lam y) z) (<= z y))))
(assert
  (forall ((y Int) (x2 Int)) (= (apply1 (lam2 y) x2) (> x2 y))))
(assert
  (not
    (forall ((x Int) (xs list))
      (= (count x (qsort xs)) (count x xs)))))
(check-sat)
