(declare-datatype pair ((pair2 (proj1-pair Int) (proj2-pair Int))))
(declare-datatype
  list3 ((nil3) (cons3 (head3 Bool) (tail3 list3))))
(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(define-fun-rec
  primEnumFromTo
  ((x Int) (y Int)) list2
  (ite (> x y) nil2 (cons2 x (primEnumFromTo (+ 1 x) y))))
(define-fun-rec
  path
  ((x Int) (y Int) (z list)) list3
  (match z
    ((nil nil3)
     ((cons x2 x3)
      (match x2
        (((pair2 u v)
          (cons3 (or (and (= u x) (= v y)) (and (= u y) (= v x)))
            (path x y x3)))))))))
(define-fun-rec
  or2
  ((x list3)) Bool
  (match x
    ((nil3 false)
     ((cons3 y xs) (or y (or2 xs))))))
(define-fun-rec
  path2
  ((x list2) (y list)) Bool
  (match x
    ((nil2 true)
     ((cons2 z x2)
      (match x2
        ((nil2 true)
         ((cons2 y2 xs)
          (and (or2 (path z y2 y)) (path2 (cons2 y2 xs) y)))))))))
(define-fun-rec
  maximum-maximum1
  ((x Int) (y list)) Int
  (match y
    ((nil x)
     ((cons z yzs)
      (match z
        (((pair2 y2 z2)
          (let ((y3 (ite (<= y2 z2) z2 y2)))
            (ite
              (<= x y3) (maximum-maximum1 y3 yzs)
              (maximum-maximum1 x yzs))))))))))
(define-fun-rec
  length
  ((x list2)) Int
  (match x
    ((nil2 0)
     ((cons2 y l) (+ 1 (length l))))))
(define-fun-rec
  last
  ((x Int) (y list2)) Int
  (match y
    ((nil2 x)
     ((cons2 z ys) (last z ys)))))
(define-fun-rec
  elem
  ((x Int) (y list2)) Bool
  (match y
    ((nil2 false)
     ((cons2 z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  unique
  ((x list2)) Bool
  (match x
    ((nil2 true)
     ((cons2 y xs) (ite (elem y xs) false (unique xs))))))
(define-fun
  tour
  ((x list2) (y list)) Bool
  (match x
    ((nil2
      (match y
        ((nil true)
         ((cons z x2) false))))
     ((cons2 x3 x4)
      (match y
        ((nil false)
         ((cons x5 vs)
          (match x5
            (((pair2 u v)
              (and (= x3 (last x3 x4))
                (and (path2 (cons2 x3 x4) (cons (pair2 u v) vs))
                  (and (unique x4)
                    (= (length (cons2 x3 x4))
                      (ite
                        (<= u v) (+ 2 (maximum-maximum1 v vs))
                        (+ 2 (maximum-maximum1 u vs)))))))))))))))))
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
    (forall ((p list2))
      (not
        (tour p
          (++ (cons (pair2 (- 3 1) 0) (dodeca (primEnumFromTo 0 (- 3 1))))
            (++ (dodeca2 3 (primEnumFromTo 0 3))
              (++ (dodeca3 3 (primEnumFromTo 0 3))
                (++
                  (cons (pair2 3 (+ (+ 3 3) (- 3 1)))
                    (dodeca4 3 (primEnumFromTo 0 (- 3 1))))
                  (++ (dodeca5 3 (primEnumFromTo 0 3))
                    (cons (pair2 (+ (+ (+ 3 3) 3) (- 3 1)) (+ (+ 3 3) 3))
                      (dodeca6 3 (primEnumFromTo 0 (- 3 1))))))))))))))
(check-sat)
