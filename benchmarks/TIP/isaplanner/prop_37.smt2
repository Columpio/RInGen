(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(define-fun-rec
  ==
  ((x Nat) (y Nat)) Bool
  (match x
    ((Z
      (match y
        ((Z true)
         ((S z) false))))
     ((S x2)
      (match y
        ((Z false)
         ((S y2) (== x2 y2))))))))
(define-fun-rec
  delete
  ((x Nat) (y list)) list
  (match y
    ((nil nil)
     ((cons z xs)
      (ite (== x z) (delete x xs) (cons z (delete x xs)))))))
(define-fun-rec
  elem
  ((x Nat) (y list)) Bool
  (match y
    ((nil false)
     ((cons z xs) (ite (== x z) true (elem x xs))))))
(assert
  (not (forall ((x Nat) (xs list)) (not (elem x (delete x xs))))))
(check-sat)
