(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(define-fun-rec
  len
  ((x list)) Nat
  (match x
    ((nil Z)
     ((cons y xs) (S (len xs))))))
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
  <=2
  ((x Nat) (y Nat)) Bool
  (match x
    ((Z true)
     ((S z)
      (match y
        ((Z false)
         ((S x2) (<=2 z x2))))))))
(assert
  (not
    (forall ((n Nat) (xs list)) (<=2 (len (delete n xs)) (len xs)))))
(check-sat)
