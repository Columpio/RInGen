(declare-datatype
  pair3 ((pair22 (proj1-pair2 Int) (proj2-pair2 Int))))
(declare-datatype
  list7 ((nil7) (cons7 (head7 Bool) (tail7 list7))))
(declare-datatype list6 ((nil6) (cons6 (head6 Int) (tail6 list6))))
(declare-datatype
  list3 ((nil2) (cons2 (head2 pair3) (tail2 list3))))
(declare-datatype
  list4 ((nil3) (cons3 (head3 list3) (tail3 list4))))
(declare-datatype B ((I) (O)))
(declare-datatype list ((nil5) (cons5 (head5 B) (tail5 list))))
(declare-datatype
  list5 ((nil4) (cons4 (head4 list) (tail4 list5))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-datatype list2 ((nil) (cons (head pair) (tail list2))))
(define-fun-rec
  primEnumFromTo
  ((x Int) (y Int)) list6
  (ite (> x y) nil6 (cons6 x (primEnumFromTo (+ 1 x) y))))
(define-fun-rec
  petersen3
  ((x Int) (y list6)) list3
  (match y
    ((nil6 nil2)
     ((cons6 z x2) (cons2 (pair22 z (+ x z)) (petersen3 x x2))))))
(define-fun-rec
  petersen2
  ((x list6)) list3
  (match x
    ((nil6 nil2)
     ((cons6 y z) (cons2 (pair22 y (+ 1 y)) (petersen2 z))))))
(define-fun-rec
  petersen
  ((x Int) (y list3)) list4
  (match y
    ((nil2 nil3)
     ((cons2 z x2)
      (match z
        (((pair22 u v)
          (cons3 (cons2 (pair22 u v) (cons2 (pair22 (+ x u) (+ x v)) nil2))
            (petersen x x2)))))))))
(define-fun-rec
  or2
  ((x list7)) Bool
  (match x
    ((nil7 false)
     ((cons7 y xs) (or y (or2 xs))))))
(define-fun-rec
  maximum-maximum1
  ((x Int) (y list3)) Int
  (match y
    ((nil2 x)
     ((cons2 z yzs)
      (match z
        (((pair22 y2 z2)
          (let ((y3 (ite (<= y2 z2) z2 y2)))
            (ite
              (<= x y3) (maximum-maximum1 y3 yzs)
              (maximum-maximum1 x yzs))))))))))
(define-fun-rec
  length
  ((x list5)) Int
  (match x
    ((nil4 0)
     ((cons4 y l) (+ 1 (length l))))))
(define-fun-rec
  last
  ((x list) (y list5)) list
  (match y
    ((nil4 x)
     ((cons4 z ys) (last z ys)))))
(define-fun-rec
  bin
  ((x Int)) list
  (ite
    (= x 0) nil5
    (ite
      (= (mod x 2) 0) (cons5 O (bin (div x 2)))
      (cons5 I (bin (div x 2))))))
(define-fun-rec
  bgraph
  ((x list3)) list2
  (match x
    ((nil2 nil)
     ((cons2 y z)
      (match y
        (((pair22 u v) (cons (pair2 (bin u) (bin v)) (bgraph z)))))))))
(define-fun-rec
  beq
  ((x list) (y list)) Bool
  (match x
    ((nil5
      (match y
        ((nil5 true)
         ((cons5 z x2) false))))
     ((cons5 x3 xs)
      (match x3
        ((I
          (match y
            ((nil5 false)
             ((cons5 x4 ys)
              (match x4
                ((I (beq xs ys))
                 (O false)))))))
         (O
          (match y
            ((nil5 false)
             ((cons5 x5 zs)
              (match x5
                ((I false)
                 (O (beq xs zs))))))))))))))
(define-fun-rec
  bpath
  ((x list) (y list) (z list2)) list7
  (match z
    ((nil nil7)
     ((cons x2 x3)
      (match x2
        (((pair2 u v)
          (cons7 (or (and (beq u x) (beq v y)) (and (beq u y) (beq v x)))
            (bpath x y x3)))))))))
(define-fun-rec
  bpath2
  ((x list5) (y list2)) Bool
  (match x
    ((nil4 true)
     ((cons4 z x2)
      (match x2
        ((nil4 true)
         ((cons4 y2 xs)
          (and (or2 (bpath z y2 y)) (bpath2 (cons4 y2 xs) y)))))))))
(define-fun-rec
  belem
  ((x list) (y list5)) list7
  (match y
    ((nil4 nil7)
     ((cons4 z x2) (cons7 (beq x z) (belem x x2))))))
(define-fun
  belem2
  ((x list) (y list5)) Bool (or2 (belem x y)))
(define-fun-rec
  bunique
  ((x list5)) Bool
  (match x
    ((nil4 true)
     ((cons4 y xs) (and (not (belem2 y xs)) (bunique xs))))))
(define-fun
  btour
  ((x list5) (y list3)) Bool
  (match x
    ((nil4
      (match y
        ((nil2 true)
         ((cons2 z x2) false))))
     ((cons4 x3 x4)
      (match y
        ((nil2 false)
         ((cons2 x5 vs)
          (match x5
            (((pair22 u v)
              (and (beq x3 (last x3 x4))
                (and (bpath2 (cons4 x3 x4) (bgraph (cons2 (pair22 u v) vs)))
                  (and (bunique x4)
                    (= (length (cons4 x3 x4))
                      (ite
                        (<= u v) (+ 1 (+ 1 (maximum-maximum1 v vs)))
                        (+ 1 (+ 1 (maximum-maximum1 u vs))))))))))))))))))
(define-fun-rec
  ++
  ((x list3) (y list3)) list3
  (match x
    ((nil2 y)
     ((cons2 z xs) (cons2 z (++ xs y))))))
(define-fun-rec
  concat2
  ((x list4)) list3
  (match x
    ((nil3 nil2)
     ((cons3 y xs) (++ y (concat2 xs))))))
(define-fun
  petersen4
  ((x Int)) list3
  (ite
    (= x 0) nil2
    (++
      (concat2
        (petersen x
          (cons2 (pair22 (- x 1) 0) (petersen2 (primEnumFromTo 0 (- x 1))))))
      (petersen3 x (primEnumFromTo 0 x)))))
(assert
  (not
    (forall ((p list5))
      (not
        (btour p
          (++
            (concat2
              (petersen 5
                (cons2 (pair22 (- 5 1) 0) (petersen2 (primEnumFromTo 0 (- 5 1))))))
            (petersen3 5 (primEnumFromTo 0 5))))))))
(check-sat)
