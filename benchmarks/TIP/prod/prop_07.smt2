(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun-rec
  qrev
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (qrev xs (cons z y))))))
(define-fun-rec
  length
  ((x list)) Nat
  (match x
    ((nil Z)
     ((cons y xs) (S (length xs))))))
(define-fun-rec
  +2
  ((x Nat) (y Nat)) Nat
  (match x
    ((Z y)
     ((S z) (S (+2 z y))))))
(assert
  (not
    (forall ((x list) (y list))
      (= (length (qrev x y)) (+2 (length x) (length y))))))
(check-sat)
