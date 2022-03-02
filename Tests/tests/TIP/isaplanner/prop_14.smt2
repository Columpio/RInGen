(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) Bool)
(define-fun-rec
  filter
  ((x fun12) (y list)) list
  (match y
    ((nil nil)
     ((cons z xs)
      (ite (apply12 x z) (cons z (filter x xs)) (filter x xs))))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(assert
  (not
    (forall ((p fun12) (xs list) (ys list))
      (= (filter p (++ xs ys)) (++ (filter p xs) (filter p ys))))))
(check-sat)
