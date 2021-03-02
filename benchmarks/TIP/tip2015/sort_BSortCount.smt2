(declare-datatype list ((nil) (cons (head Int) (tail list))))
(define-fun
  sort2
  ((x Int) (y Int)) list
  (ite (<= x y) (cons x (cons y nil)) (cons y (cons x nil))))
(define-funs-rec
  ((evens
    ((x list)) list)
   (odds
    ((x list)) list))
  ((match x
     ((nil nil)
      ((cons y xs) (cons y (odds xs)))))
   (match x
     ((nil nil)
      ((cons y xs) (evens xs))))))
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
  pairs
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z x2)
      (match y
        ((nil (cons z x2))
         ((cons x3 x4) (++ (sort2 z x3) (pairs x2 x4)))))))))
(define-fun
  stitch
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (pairs xs y))))))
(define-fun-rec
  bmerge
  ((x list) (y list)) list
  (match x
    ((nil nil)
     ((cons z x2)
      (match y
        ((nil (cons z x2))
         ((cons x3 x4)
          (let
            ((fail
                (stitch (bmerge (evens (cons z x2)) (evens (cons x3 x4)))
                  (bmerge (odds (cons z x2)) (odds (cons x3 x4))))))
            (match x2
              ((nil
                (match x4
                  ((nil (sort2 z x3))
                   ((cons x5 x6) fail))))
               ((cons x7 x8) fail)))))))))))
(define-fun-rec
  bsort
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y z)
      (match z
        ((nil (cons y nil))
         ((cons x2 x3)
          (bmerge (bsort (evens (cons y (cons x2 x3))))
            (bsort (odds (cons y (cons x2 x3))))))))))))
(assert
  (not
    (forall ((x Int) (xs list))
      (= (count x (bsort xs)) (count x xs)))))
(check-sat)
