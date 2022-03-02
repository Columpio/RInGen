(declare-datatype Nat ((S (proj1-S Nat)) (Z)))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(define-fun-rec
  length
  ((x list)) Nat
  (match x
    ((nil Z)
     ((cons y xs) (S (length xs))))))
(define-fun-rec
  <2
  ((x Nat) (y Nat)) Bool
  (match x
    (((S z)
      (match y
        (((S y2) (<2 z y2))
         (Z false))))
     (Z
      (match y
        (((S x2) true)
         (Z false)))))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  rotate
  ((x Nat) (y list)) list
  (match x
    (((S z)
      (match y
        ((nil nil)
         ((cons x2 x3) (rotate z (++ x3 (cons x2 nil)))))))
     (Z y))))
(assert
  (not
    (forall ((n Nat) (m Nat) (ys list) (xs list))
      (=> (<2 n (length xs))
        (=> (<2 m (length ys))
          (=> (= xs ys)
            (=> (distinct (rotate (S Z) xs) xs)
              (=> (= (rotate n xs) (rotate m ys)) (= n m)))))))))
(check-sat)
