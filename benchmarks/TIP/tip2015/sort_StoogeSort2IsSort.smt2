(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
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
  insert2
  ((x Int) (y list)) list
  (match y
    ((nil (cons x nil))
     ((cons z xs)
      (ite (<= x z) (cons x (cons z xs)) (cons z (insert2 x xs)))))))
(define-fun-rec
  isort
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y xs) (insert2 y (isort xs))))))
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
(assert (not (forall ((xs list)) (= (stoogesort2 xs) (isort xs)))))
(check-sat)
