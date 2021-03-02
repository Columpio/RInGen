(declare-sort sk 0)
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun-rec
  zip
  ((x list2) (y list2)) list
  (match x
    ((nil2 nil)
     ((cons2 z x2)
      (match y
        ((nil2 nil)
         ((cons2 x3 x4) (cons (pair2 z x3) (zip x2 x4)))))))))
(define-fun-rec
  take
  ((x Nat) (y list2)) list2
  (match x
    ((Z nil2)
     ((S z)
      (match y
        ((nil2 nil2)
         ((cons2 x2 x3) (cons2 x2 (take z x3)))))))))
(define-fun-rec
  len
  ((x list2)) Nat
  (match x
    ((nil2 Z)
     ((cons2 y xs) (S (len xs))))))
(define-fun-rec
  drop
  ((x Nat) (y list2)) list2
  (match x
    ((Z y)
     ((S z)
      (match y
        ((nil2 nil2)
         ((cons2 x2 x3) (drop z x3))))))))
(define-fun-rec
  ++2
  ((x list2) (y list2)) list2
  (match x
    ((nil2 y)
     ((cons2 z xs) (cons2 z (++2 xs y))))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(assert
  (not
    (forall ((xs list2) (ys list2) (zs list2))
      (= (zip (++2 xs ys) zs)
        (++ (zip xs (take (len xs) zs)) (zip ys (drop (len xs) zs)))))))
(check-sat)
