(declare-datatype list ((nil) (cons (head Int) (tail list))))
(define-fun-rec
  merge
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs)
      (match y
        ((nil (cons z xs))
         ((cons y2 ys)
          (ite
            (<= z y2) (cons z (merge xs (cons y2 ys)))
            (cons y2 (merge (cons z xs) ys))))))))))
(assert
  (not
    (forall ((xs list) (ys list) (zs list))
      (=> (= (merge xs ys) (merge ys xs))
        (=> (= (merge xs zs) (merge zs xs))
          (= (merge ys zs) (merge zs ys)))))))
(check-sat)
