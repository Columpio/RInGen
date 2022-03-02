(declare-sort sk 0)
(declare-sort fun1 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun apply1 (fun1 sk) sk)
(define-fun-rec
  take
  ((x Nat) (y list)) list
  (match x
    ((Z nil)
     ((S z)
      (match y
        ((nil nil)
         ((cons x2 x3) (cons x2 (take z x3)))))))))
(define-fun-rec
  map2
  ((x fun1) (y list)) list
  (match y
    ((nil nil)
     ((cons z xs) (cons (apply1 x z) (map2 x xs))))))
(assert
  (not
    (forall ((n Nat) (f fun1) (xs list))
      (= (take n (map2 f xs)) (map2 f (take n xs))))))
(check-sat)
