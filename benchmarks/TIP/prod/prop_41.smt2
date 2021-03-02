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
(define-fun
  &&
  ((x Bool) (y Bool)) Bool (ite x y false))
(define-fun-rec
  subset2
  ((x list) (y list)) Bool
  (match x
    ((nil true)
     ((cons z xs) (&& (elem z y) (subset2 xs y))))))
(assert
  (not
    (forall ((x list) (y list))
      (=> (subset2 x y) (= (intersect2 x y) x)))))
(check-sat)
