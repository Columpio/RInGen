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
  ordered
  ((x list)) Bool
  (match x
    ((nil true)
     ((cons y z)
      (match z
        ((nil true)
         ((cons y2 xs) (and (<= y y2) (ordered (cons y2 xs))))))))))
(define-fun-rec
  nmsorttd-half1
  ((x Int)) Int
  (ite (= x 1) 0 (ite (= x 0) 0 (+ 1 (nmsorttd-half1 (- x 2))))))
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
  drop
  ((x Int) (y list)) list
  (ite
    (<= x 0) y
    (match y
      ((nil nil)
       ((cons z xs1) (drop (- x 1) xs1))))))
(define-fun-rec
  nmsorttd
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y z)
      (match z
        ((nil (cons y nil))
         ((cons x2 x3)
          (let ((k (nmsorttd-half1 (length (cons y (cons x2 x3))))))
            (lmerge (nmsorttd (take k (cons y (cons x2 x3))))
              (nmsorttd (drop k (cons y (cons x2 x3)))))))))))))
(assert (not (forall ((xs list)) (ordered (nmsorttd xs)))))
(check-sat)
