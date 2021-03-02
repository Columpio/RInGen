(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair Bool) (proj2-pair list))))
(define-fun-rec
  count
  ((x Int) (y list)) Int
  (match y
    ((nil 0)
     ((cons z ys) (ite (= x z) (+ 1 (count x ys)) (count x ys))))))
(define-fun-rec
  bubble
  ((x list)) pair
  (match x
    ((nil (pair2 false nil))
     ((cons y z)
      (match z
        ((nil (pair2 false (cons y nil)))
         ((cons y2 xs)
          (ite
            (<= y y2)
            (match (bubble (cons y2 xs))
              (((pair2 b12 ys12) (pair2 b12 (cons y ys12)))))
            (match (bubble (cons y xs))
              (((pair2 b1 ys1) (pair2 true (cons y2 ys1)))))))))))))
(define-fun-rec
  bubsort
  ((x list)) list
  (match (bubble x) (((pair2 c ys1) (ite c (bubsort ys1) x)))))
(assert
  (not
    (forall ((x Int) (xs list))
      (= (count x (bubsort xs)) (count x xs)))))
(check-sat)
