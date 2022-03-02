(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun-rec
  length
  ((x list)) Nat
  (match x
    ((nil Z)
     ((cons y xs) (S (length xs))))))
(define-fun-rec
  half
  ((x Nat)) Nat
  (match x
    ((Z Z)
     ((S y)
      (match y
        ((Z Z)
         ((S z) (S (half z)))))))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(assert
  (not
    (forall ((x list) (y list))
      (= (half (length (++ x y))) (half (length (++ y x)))))))
(check-sat)
