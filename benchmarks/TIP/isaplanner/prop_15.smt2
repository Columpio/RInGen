(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(define-fun-rec
  len
  ((x list)) Nat
  (match x
    ((nil Z)
     ((cons y xs) (S (len xs))))))
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
    (forall ((x Nat) (xs list)) (= (len (ins x xs)) (S (len xs))))))
(check-sat)
