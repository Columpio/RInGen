(declare-datatype pair ((pair2 (proj1-pair Int) (proj2-pair Int))))
(declare-datatype
  list4 ((nil4) (cons4 (head4 Bool) (tail4 list4))))
(declare-datatype list3 ((nil3) (cons3 (head3 Int) (tail3 list3))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(declare-datatype
  list2 ((nil2) (cons2 (head2 list) (tail2 list2))))
(declare-datatype Maybe ((Nothing) (Just (proj1-Just Int))))
(define-fun-rec
  primEnumFromTo
  ((x Int) (y Int)) list3
  (ite (> x y) nil3 (cons3 x (primEnumFromTo (+ 1 x) y))))
(define-fun-rec
  petersen3
  ((x Int) (y list3)) list
  (match y
    ((nil3 nil)
     ((cons3 z x2) (cons (pair2 z (+ x z)) (petersen3 x x2))))))
(define-fun-rec
  petersen2
  ((x list3)) list
  (match x
    ((nil3 nil)
     ((cons3 y z) (cons (pair2 y (+ 1 y)) (petersen2 z))))))
(define-fun-rec
  petersen
  ((x Int) (y list)) list2
  (match y
    ((nil nil2)
     ((cons z x2)
      (match z
        (((pair2 u v)
          (cons2 (cons (pair2 u v) (cons (pair2 (+ x u) (+ x v)) nil))
            (petersen x x2)))))))))
(define-fun-rec
  index
  ((x list3) (y Int)) Maybe
  (match x
    ((nil3 Nothing)
     ((cons3 z xs) (ite (= y 0) (Just z) (index xs (- y 1)))))))
(define-fun-rec
  formula
  ((x list3)) list4
  (match x
    ((nil3 nil4)
     ((cons3 y z) (cons4 (< y 3) (formula z))))))
(define-fun-rec
  colouring
  ((a list3) (x list)) list4
  (match x
    ((nil nil4)
     ((cons y z)
      (match y
        (((pair2 u v)
          (match (index a u)
            ((Nothing (cons4 false (colouring a z)))
             ((Just c1)
              (match (index a v)
                ((Nothing (cons4 false (colouring a z)))
                 ((Just c2) (cons4 (distinct c1 c2) (colouring a z)))))))))))))))
(define-fun-rec
  and2
  ((x list4)) Bool
  (match x
    ((nil4 true)
     ((cons4 y xs) (and y (and2 xs))))))
(define-fun
  colouring2
  ((x list) (y list3)) Bool (and2 (colouring y x)))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  concat2
  ((x list2)) list
  (match x
    ((nil2 nil)
     ((cons2 y xs) (++ y (concat2 xs))))))
(define-fun
  petersen4
  ((x Int)) list
  (ite
    (= x 0) nil
    (++
      (concat2
        (petersen x
          (cons (pair2 (- x 1) 0) (petersen2 (primEnumFromTo 0 (- x 1))))))
      (petersen3 x (primEnumFromTo 0 x)))))
(assert
  (not
    (forall ((a list3))
      (or
        (not
          (colouring2
            (++
              (concat2
                (petersen 7
                  (cons (pair2 (- 7 1) 0) (petersen2 (primEnumFromTo 0 (- 7 1))))))
              (petersen3 7 (primEnumFromTo 0 7)))
            a))
        (not (and2 (formula a)))))))
(check-sat)
