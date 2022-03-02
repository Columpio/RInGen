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
  take2
  ((x Nat) (y list2)) list2
  (match x
    ((Z nil2)
     ((S z)
      (match y
        ((nil2 nil2)
         ((cons2 x2 x3) (cons2 x2 (take2 z x3)))))))))
(define-fun-rec
  take
  ((x Nat) (y list)) list
  (match x
    ((Z nil)
     ((S z)
      (match y
        ((nil nil)
         ((cons x2 x3) (cons x2 (take z x3)))))))))
(assert
  (not
    (forall ((n Nat) (xs list2) (ys list2))
      (= (take n (zip xs ys)) (zip (take2 n xs) (take2 n ys))))))
(check-sat)
