(declare-datatype Nat ((S (proj1-S Nat)) (Z)))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(define-fun-rec
  eqNat
  ((x Nat) (y Nat)) Bool
  (match x
    (((S z)
      (match y
        (((S y2) (eqNat z y2))
         (Z false))))
     (Z
      (match y
        (((S x2) false)
         (Z true)))))))
(define-fun
  barbar
  ((x Bool) (y Bool)) Bool (ite x true y))
(define-fun-rec
  elem
  ((x Nat) (y list)) Bool
  (match y
    ((nil false)
     ((cons z xs) (barbar (eqNat x z) (elem x xs))))))
(define-fun-rec
  union2
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs)
      (ite (elem z y) (union2 xs y) (cons z (union2 xs y)))))))
(assert (not (forall ((xs list)) (= (union2 xs xs) xs))))
(check-sat)
