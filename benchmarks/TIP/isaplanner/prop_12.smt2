(declare-sort sk 0)
(declare-sort fun1 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun apply1 (fun1 sk) sk)
(define-fun-rec
  map2
  ((x fun1) (y list)) list
  (match y
    ((nil nil)
     ((cons z xs) (cons (apply1 x z) (map2 x xs))))))
(define-fun-rec
  drop
  ((x Nat) (y list)) list
  (match x
    ((Z y)
     ((S z)
      (match y
        ((nil nil)
         ((cons x2 x3) (drop z x3))))))))
(assert
  (not
    (forall ((n Nat) (f fun1) (xs list))
      (= (drop n (map2 f xs)) (map2 f (drop n xs))))))
(check-sat)
