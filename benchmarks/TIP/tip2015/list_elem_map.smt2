(declare-sort sk 0)
(declare-sort fun1 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun apply1 (fun1 sk) sk)
(define-fun-rec
  map2
  ((f fun1) (x list)) list
  (match x
    ((nil nil)
     ((cons y xs) (cons (apply1 f y) (map2 f xs))))))
(define-fun-rec
  elem
  ((x sk) (y list)) Bool
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(assert
  (not
    (forall ((y sk) (f fun1) (xs list))
      (=> (elem y (map2 f xs))
        (exists ((x sk)) (and (= (apply1 f x) y) (elem y xs)))))))
(check-sat)
