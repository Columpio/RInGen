(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(define-fun-rec
  len
  ((x list)) Nat
  (match x
    ((nil Z)
     ((cons y xs) (S (len xs))))))
(define-fun-rec
  last
  ((x list)) Nat
  (match x
    ((nil Z)
     ((cons y z)
      (match z
        ((nil y)
         ((cons x2 x3) (last (cons x2 x3)))))))))
(define-fun-rec
  drop
  ((x Nat) (y list)) list
  (match x
    ((Z y)
     ((S z)
      (match y
        ((nil nil)
         ((cons x2 x3) (drop z x3))))))))
(define-fun-rec
  <2
  ((x Nat) (y Nat)) Bool
  (match y
    ((Z false)
     ((S z)
      (match x
        ((Z true)
         ((S x2) (<2 x2 z))))))))
(assert
  (not
    (forall ((n Nat) (xs list))
      (=> (<2 n (len xs)) (= (last (drop n xs)) (last xs))))))
(check-sat)
