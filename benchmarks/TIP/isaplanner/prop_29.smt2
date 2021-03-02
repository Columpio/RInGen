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
  elem
  ((x Nat) (y list)) Bool
  (match y
    ((nil false)
     ((cons z xs) (ite (== x z) true (elem x xs))))))
(define-fun-rec
  ins1
  ((x Nat) (y list)) list
  (match y
    ((nil (cons x nil))
     ((cons z xs) (ite (== x z) (cons z xs) (cons z (ins1 x xs)))))))
(assert (not (forall ((x Nat) (xs list)) (elem x (ins1 x xs)))))
(check-sat)
