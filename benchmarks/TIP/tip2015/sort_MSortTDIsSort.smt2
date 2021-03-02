(declare-datatype list ((nil) (cons (head Int) (tail list))))
(define-fun-rec
  take
  ((x Int) (y list)) list
  (ite
    (<= x 0) nil
    (match y
      ((nil nil)
       ((cons z xs) (cons z (take (- x 1) xs)))))))
(define-fun-rec
  lmerge
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z x2)
      (match y
        ((nil (cons z x2))
         ((cons x3 x4)
          (ite
            (<= z x3) (cons z (lmerge x2 (cons x3 x4)))
            (cons x3 (lmerge (cons z x2) x4))))))))))
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
(define-fun-rec
  msorttd
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y z)
      (match z
        ((nil (cons y nil))
         ((cons x2 x3)
          (let ((k (div (length (cons y (cons x2 x3))) 2)))
            (lmerge (msorttd (take k (cons y (cons x2 x3))))
              (msorttd (drop k (cons y (cons x2 x3)))))))))))))
(assert (not (forall ((xs list)) (= (msorttd xs) (isort xs)))))
(check-sat)
