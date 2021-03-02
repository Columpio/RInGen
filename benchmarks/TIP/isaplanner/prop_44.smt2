(declare-sort sk 0)
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(define-fun-rec
  zip
  ((x list2) (y list2)) list
  (match x
    ((nil2 nil)
     ((cons2 z x2)
      (match y
        ((nil2 nil)
         ((cons2 x3 x4) (cons (pair2 z x3) (zip x2 x4)))))))))
(define-fun
  zipConcat
  ((x sk) (y list2) (z list2)) list
  (match z
    ((nil2 nil)
     ((cons2 y2 ys) (cons (pair2 x y2) (zip y ys))))))
(assert
  (not
    (forall ((x sk) (xs list2) (ys list2))
      (= (zip (cons2 x xs) ys) (zipConcat x xs ys)))))
(check-sat)
