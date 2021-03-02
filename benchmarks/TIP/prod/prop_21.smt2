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
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  rotate
  ((x Nat) (y list)) list
  (match x
    ((Z y)
     ((S z)
      (match y
        ((nil nil)
         ((cons x2 x3) (rotate z (++ x3 (cons x2 nil))))))))))
(assert
  (not
    (forall ((x list) (y list))
      (= (rotate (length x) (++ x y)) (++ y x)))))
(check-sat)
