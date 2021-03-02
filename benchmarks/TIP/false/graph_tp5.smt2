(declare-datatype pair ((pair2 (proj1-pair Int) (proj2-pair Int))))
(declare-datatype
  list4 ((nil4) (cons4 (head4 Bool) (tail4 list4))))
(declare-datatype list3 ((nil3) (cons3 (head3 Int) (tail3 list3))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(declare-datatype
  list2 ((nil2) (cons2 (head2 list) (tail2 list2))))
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
  path
  ((x Int) (y Int) (z list)) list4
  (match z
    ((nil nil4)
     ((cons x2 x3)
      (match x2
        (((pair2 u v)
          (cons4 (or (and (= u x) (= v y)) (and (= u y) (= v x)))
            (path x y x3)))))))))
(define-fun-rec
  or2
  ((x list4)) Bool
  (match x
    ((nil4 false)
     ((cons4 y xs) (or y (or2 xs))))))
(define-fun-rec
  path2
  ((x list3) (y list)) Bool
  (match x
    ((nil3 true)
     ((cons3 z x2)
      (match x2
        ((nil3 true)
         ((cons3 y2 xs)
          (and (or2 (path z y2 y)) (path2 (cons3 y2 xs) y)))))))))
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
  ((x list3)) Int
  (match x
    ((nil3 0)
     ((cons3 y l) (+ 1 (length l))))))
(define-fun-rec
  last
  ((x Int) (y list3)) Int
  (match y
    ((nil3 x)
     ((cons3 z ys) (last z ys)))))
(define-fun-rec
  elem
  ((x Int) (y list3)) Bool
  (match y
    ((nil3 false)
     ((cons3 z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  unique
  ((x list3)) Bool
  (match x
    ((nil3 true)
     ((cons3 y xs) (ite (elem y xs) false (unique xs))))))
(define-fun
  tour
  ((x list3) (y list)) Bool
  (match x
    ((nil3
      (match y
        ((nil true)
         ((cons z x2) false))))
     ((cons3 x3 x4)
      (match y
        ((nil false)
         ((cons x5 vs)
          (match x5
            (((pair2 u v)
              (and (= x3 (last x3 x4))
                (and (path2 (cons3 x3 x4) (cons (pair2 u v) vs))
                  (and (unique x4)
                    (= (length (cons3 x3 x4))
                      (ite
                        (<= u v) (+ 2 (maximum-maximum1 v vs))
                        (+ 2 (maximum-maximum1 u vs)))))))))))))))))
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
    (forall ((p list3))
      (not
        (tour p
          (++
            (concat2
              (petersen 5
                (cons (pair2 (- 5 1) 0) (petersen2 (primEnumFromTo 0 (- 5 1))))))
            (petersen3 5 (primEnumFromTo 0 5))))))))
(check-sat)
