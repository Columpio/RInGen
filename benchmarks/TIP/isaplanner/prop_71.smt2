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
  <2
  ((x Nat) (y Nat)) Bool
  (match y
    ((Z false)
     ((S z)
      (match x
        ((Z true)
         ((S x2) (<2 x2 z))))))))
(define-fun-rec
  ins
  ((x Nat) (y list)) list
  (match y
    ((nil (cons x nil))
     ((cons z xs)
      (ite (<2 x z) (cons x (cons z xs)) (cons z (ins x xs)))))))
(assert
  (not
    (forall ((x Nat) (y Nat) (xs list))
      (=> (not (== x y)) (= (elem x (ins y xs)) (elem x xs))))))
(check-sat)
