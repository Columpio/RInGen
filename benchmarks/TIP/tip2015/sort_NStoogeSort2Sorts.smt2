(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(define-fun-rec
  twoThirds
  ((x Int)) Int
  (ite
    (= x 2) 1
    (ite (= x 1) 1 (ite (= x 0) 0 (+ 2 (twoThirds (- x 3)))))))
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
  ordered
  ((x list)) Bool
  (match x
    ((nil true)
     ((cons y z)
      (match z
        ((nil true)
         ((cons y2 xs) (and (<= y y2) (ordered (cons y2 xs))))))))))
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
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-funs-rec
  ((nstooge2sort2
    ((x list)) list)
   (nstoogesort2
    ((x list)) list)
   (nstooge2sort1
    ((x list)) list))
  ((match (splitAt (twoThirds (length x)) x)
     (((pair2 ys1 zs) (++ (nstoogesort2 ys1) zs))))
   (match x
     ((nil nil)
      ((cons y z)
       (match z
         ((nil (cons y nil))
          ((cons y2 x2)
           (match x2
             ((nil (sort2 y y2))
              ((cons x3 x4)
               (nstooge2sort2
                 (nstooge2sort1
                   (nstooge2sort2 (cons y (cons y2 (cons x3 x4)))))))))))))))
   (match (splitAt (third (length x)) x)
     (((pair2 ys1 zs) (++ ys1 (nstoogesort2 zs)))))))
(assert (not (forall ((xs list)) (ordered (nstoogesort2 xs)))))
(check-sat)
