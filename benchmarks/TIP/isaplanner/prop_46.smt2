(declare-sort Any 0)
(declare-sort sk 0)
(declare-datatype
  pair3 ((pair22 (proj1-pair2 sk) (proj2-pair2 sk))))
(declare-datatype pair ((pair2 (proj1-pair Any) (proj2-pair sk))))
(declare-datatype list4 ((nil4) (cons4 (head4 sk) (tail4 list4))))
(declare-datatype
  list3 ((nil3) (cons3 (head3 pair3) (tail3 list3))))
(declare-datatype
  list2 ((nil2) (cons2 (head2 pair) (tail2 list2))))
(declare-datatype list ((nil) (cons (head Any) (tail list))))
(define-fun-rec
  zip2
  ((x list4) (y list4)) list3
  (match x
    ((nil4 nil3)
     ((cons4 z x2)
      (match y
        ((nil4 nil3)
         ((cons4 x3 x4) (cons3 (pair22 z x3) (zip2 x2 x4)))))))))
(define-fun-rec
  zip
  ((x list) (y list4)) list2
  (match x
    ((nil nil2)
     ((cons z x2)
      (match y
        ((nil4 nil2)
         ((cons4 x3 x4) (cons2 (pair2 z x3) (zip x2 x4)))))))))
(assert (not (forall ((xs list4)) (= (zip nil xs) nil2))))
(check-sat)
