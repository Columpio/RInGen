(declare-sort sk 0)
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(define-fun-rec
  unpair
  ((x list)) list2
  (match x
    ((nil nil2)
     ((cons y xys)
      (match y (((pair2 z y2) (cons2 z (cons2 y2 (unpair xys))))))))))
(define-fun-rec
  pairs
  ((x list2)) list
  (match x
    ((nil2 nil)
     ((cons2 y z)
      (match z
        ((nil2 nil)
         ((cons2 y2 xs) (cons (pair2 y y2) (pairs xs)))))))))
(define-fun-rec
  length
  ((x list2)) Int
  (match x
    ((nil2 0)
     ((cons2 y l) (+ 1 (length l))))))
(assert
  (not
    (forall ((xs list2))
      (=> (= (mod (length xs) 2) 0) (= (unpair (pairs xs)) xs)))))
(check-sat)
