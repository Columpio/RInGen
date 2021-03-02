(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-fun lam (Int) fun12)
(declare-const lam2 fun1)
(declare-fun apply1 (fun1 Int) fun12)
(declare-fun apply12 (fun12 Int) Bool)
(define-fun-rec
  take
  ((x Int) (y list)) list
  (ite
    (<= x 0) nil
    (match y
      ((nil nil)
       ((cons z xs) (cons z (take (- x 1) xs)))))))
(define-fun
  sort2
  ((x Int) (y Int)) list
  (ite (<= x y) (cons x (cons y nil)) (cons y (cons x nil))))
(define-fun-rec
  length
  ((x list)) Int
  (match x
    ((nil 0)
     ((cons y l) (+ 1 (length l))))))
(define-fun-rec
  elem
  ((x Int) (y list)) Bool
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  drop
  ((x Int) (y list)) list
  (ite
    (<= x 0) y
    (match y
      ((nil nil)
       ((cons z xs1) (drop (- x 1) xs1))))))
(define-fun
  splitAt
  ((x Int) (y list)) pair (pair2 (take x y) (drop x y)))
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
(define-funs-rec
  ((stooge2sort2
    ((x list)) list)
   (stoogesort2
    ((x list)) list)
   (stooge2sort1
    ((x list)) list))
  ((match (splitAt (div (+ (* 2 (length x)) 1) 3) x)
     (((pair2 ys1 zs) (++ (stoogesort2 ys1) zs))))
   (match x
     ((nil nil)
      ((cons y z)
       (match z
         ((nil (cons y nil))
          ((cons y2 x2)
           (match x2
             ((nil (sort2 y y2))
              ((cons x3 x4)
               (stooge2sort2
                 (stooge2sort1
                   (stooge2sort2 (cons y (cons y2 (cons x3 x4)))))))))))))))
   (match (splitAt (div (length x) 3) x)
     (((pair2 ys1 zs) (++ ys1 (stoogesort2 zs)))))))
(assert (forall ((x4 Int)) (= (apply1 lam2 x4) (lam x4))))
(assert
  (forall ((x4 Int) (x5 Int)) (= (apply12 (lam x4) x5) (= x4 x5))))
(assert
  (not (forall ((xs list)) (isPermutation (stoogesort2 xs) xs))))
(check-sat)
