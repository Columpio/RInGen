(declare-datatype pair ((pair2 (proj1-pair Int) (proj2-pair Int))))
(declare-datatype
  list3 ((nil3) (cons3 (head3 Bool) (tail3 list3))))
(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(declare-datatype Maybe ((Nothing) (Just (proj1-Just Int))))
(define-fun-rec
  primEnumFromTo
  ((x Int) (y Int)) list2
  (ite (> x y) nil2 (cons2 x (primEnumFromTo (+ 1 x) y))))
(define-fun-rec
  index
  ((x list2) (y Int)) Maybe
  (match x
    ((nil2 Nothing)
     ((cons2 z xs) (ite (= y 0) (Just z) (index xs (- y 1)))))))
(define-fun-rec
  formula
  ((x list2)) list3
  (match x
    ((nil2 nil3)
     ((cons2 y z) (cons3 (< y 3) (formula z))))))
(define-fun-rec
  dodeca6
  ((x Int) (y list2)) list
  (match y
    ((nil2 nil)
     ((cons2 z x2)
      (cons (pair2 (+ (+ (+ x x) x) z) (+ (+ (+ x x) x) (+ 1 z)))
        (dodeca6 x x2))))))
(define-fun-rec
  dodeca5
  ((x Int) (y list2)) list
  (match y
    ((nil2 nil)
     ((cons2 z x2)
      (cons (pair2 (+ (+ x x) z) (+ (+ (+ x x) x) z)) (dodeca5 x x2))))))
(define-fun-rec
  dodeca4
  ((x Int) (y list2)) list
  (match y
    ((nil2 nil)
     ((cons2 z x2)
      (cons (pair2 (+ x (+ 1 z)) (+ (+ x x) z)) (dodeca4 x x2))))))
(define-fun-rec
  dodeca3
  ((x Int) (y list2)) list
  (match y
    ((nil2 nil)
     ((cons2 z x2)
      (cons (pair2 (+ x z) (+ (+ x x) z)) (dodeca3 x x2))))))
(define-fun-rec
  dodeca2
  ((x Int) (y list2)) list
  (match y
    ((nil2 nil)
     ((cons2 z x2) (cons (pair2 z (+ x z)) (dodeca2 x x2))))))
(define-fun-rec
  dodeca
  ((x list2)) list
  (match x
    ((nil2 nil)
     ((cons2 y z) (cons (pair2 y (+ 1 y)) (dodeca z))))))
(define-fun-rec
  colouring
  ((a list2) (x list)) list3
  (match x
    ((nil nil3)
     ((cons y z)
      (match y
        (((pair2 u v)
          (match (index a u)
            ((Nothing (cons3 false (colouring a z)))
             ((Just c1)
              (match (index a v)
                ((Nothing (cons3 false (colouring a z)))
                 ((Just c2) (cons3 (distinct c1 c2) (colouring a z)))))))))))))))
(define-fun-rec
  and2
  ((x list3)) Bool
  (match x
    ((nil3 true)
     ((cons3 y xs) (and y (and2 xs))))))
(define-fun
  colouring2
  ((x list) (y list2)) Bool (and2 (colouring y x)))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun
  dodeca7
  ((x Int)) list
  (ite
    (= x 0) nil
    (++ (cons (pair2 (- x 1) 0) (dodeca (primEnumFromTo 0 (- x 1))))
      (++ (dodeca2 x (primEnumFromTo 0 x))
        (++ (dodeca3 x (primEnumFromTo 0 x))
          (++
            (cons (pair2 x (+ (+ x x) (- x 1)))
              (dodeca4 x (primEnumFromTo 0 (- x 1))))
            (++ (dodeca5 x (primEnumFromTo 0 x))
              (cons (pair2 (+ (+ (+ x x) x) (- x 1)) (+ (+ x x) x))
                (dodeca6 x (primEnumFromTo 0 (- x 1)))))))))))
(assert
  (not
    (forall ((a list2))
      (or
        (not
          (colouring2
            (++ (cons (pair2 (- 5 1) 0) (dodeca (primEnumFromTo 0 (- 5 1))))
              (++ (dodeca2 5 (primEnumFromTo 0 5))
                (++ (dodeca3 5 (primEnumFromTo 0 5))
                  (++
                    (cons (pair2 5 (+ (+ 5 5) (- 5 1)))
                      (dodeca4 5 (primEnumFromTo 0 (- 5 1))))
                    (++ (dodeca5 5 (primEnumFromTo 0 5))
                      (cons (pair2 (+ (+ (+ 5 5) 5) (- 5 1)) (+ (+ 5 5) 5))
                        (dodeca6 5 (primEnumFromTo 0 (- 5 1)))))))))
            a))
        (not (and2 (formula a)))))))
(check-sat)
