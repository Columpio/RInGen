(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(define-fun
  barbar
  ((x Bool) (y Bool)) Bool (ite x true y))
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
     ((cons z xs) (barbar (== x z) (elem x xs))))))
(define-fun-rec
  intersect2
  ((x list) (y list)) list
  (match x
    ((nil nil)
     ((cons z xs)
      (ite (elem z y) (cons z (intersect2 xs y)) (intersect2 xs y))))))
(assert
  (not
    (forall ((x Nat) (y list) (z list))
      (=> (elem x y) (=> (elem x z) (elem x (intersect2 y z)))))))
(check-sat)
