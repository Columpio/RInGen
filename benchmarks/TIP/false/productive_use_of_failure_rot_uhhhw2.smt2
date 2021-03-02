(declare-datatype Nat ((S (proj1-S Nat)) (Z)))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(define-fun-rec
  length
  ((x list)) Nat
  (match x
    ((nil Z)
     ((cons y xs) (S (length xs))))))
(assert
  (not
    (forall ((xs list) (ys list))
      (=> (= (length xs) (length ys)) (= xs ys)))))
(check-sat)
