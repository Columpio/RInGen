(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(define-fun-rec
  last
  ((x list)) Nat
  (match x
    ((nil Z)
     ((cons y z)
      (match z
        ((nil y)
         ((cons x2 x3) (last (cons x2 x3)))))))))
(define-fun
  lastOfTwo
  ((x list) (y list)) Nat
  (match y
    ((nil (last x))
     ((cons z x2) (last (cons z x2))))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(assert
  (not
    (forall ((xs list) (ys list))
      (= (last (++ xs ys)) (lastOfTwo xs ys)))))
(check-sat)
