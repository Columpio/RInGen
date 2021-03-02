(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) Bool)
(define-fun-rec
  len
  ((x list)) Nat
  (match x
    ((nil Z)
     ((cons y xs) (S (len xs))))))
(define-fun-rec
  filter
  ((x fun12) (y list)) list
  (match y
    ((nil nil)
     ((cons z xs)
      (ite (apply12 x z) (cons z (filter x xs)) (filter x xs))))))
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
    (forall ((p fun12) (xs list)) (<=2 (len (filter p xs)) (len xs)))))
(check-sat)
