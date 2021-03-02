(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(define-fun-rec
  third
  ((x Int)) Int
  (ite
    (= x 2) 0 (ite (= x 1) 0 (ite (= x 0) 0 (+ 1 (third (- x 3)))))))
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
  reverse
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y xs) (++ (reverse xs) (cons y nil))))))
(define-funs-rec
  ((nstooge1sort2
    ((x list)) list)
   (nstoogesort
    ((x list)) list)
   (nstooge1sort1
    ((x list)) list))
  ((match (splitAt (third (length x)) (reverse x))
     (((pair2 ys1 zs1) (++ (nstoogesort zs1) (reverse ys1)))))
   (match x
     ((nil nil)
      ((cons y z)
       (match z
         ((nil (cons y nil))
          ((cons y2 x2)
           (match x2
             ((nil (sort2 y y2))
              ((cons x3 x4)
               (nstooge1sort2
                 (nstooge1sort1
                   (nstooge1sort2 (cons y (cons y2 (cons x3 x4)))))))))))))))
   (match (splitAt (third (length x)) x)
     (((pair2 ys1 zs) (++ ys1 (nstoogesort zs)))))))
(assert
  (not
    (forall ((x Int) (xs list))
      (= (count x (nstoogesort xs)) (count x xs)))))
(check-sat)
