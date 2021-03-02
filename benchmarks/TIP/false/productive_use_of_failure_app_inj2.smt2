(declare-datatype Nat ((S (proj1-S Nat)) (Z)))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(assert
  (not
    (forall ((xs list) (ys list) (zs list))
      (=> (= (++ xs ys) (++ zs ys)) (= xs zs)))))
(check-sat)
