(declare-datatype
  pair3 ((pair22 (proj1-pair2 Int) (proj2-pair2 Int))))
(declare-datatype
  list6 ((nil6) (cons6 (head6 Bool) (tail6 list6))))
(declare-datatype list5 ((nil5) (cons5 (head5 Int) (tail5 list5))))
(declare-datatype
  list3 ((nil2) (cons2 (head2 pair3) (tail2 list3))))
(declare-datatype B ((I) (O)))
(declare-datatype list ((nil4) (cons4 (head4 B) (tail4 list))))
(declare-datatype
  list4 ((nil3) (cons3 (head3 list) (tail3 list4))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-datatype list2 ((nil) (cons (head pair) (tail list2))))
(define-fun-rec
  primEnumFromTo
  ((x Int) (y Int)) list5
  (ite (> x y) nil5 (cons5 x (primEnumFromTo (+ 1 x) y))))
(define-fun-rec
  or2
  ((x list6)) Bool
  (match x
    ((nil6 false)
     ((cons6 y xs) (or y (or2 xs))))))
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
  ((x list4)) Int
  (match x
    ((nil3 0)
     ((cons3 y l) (+ 1 (length l))))))
(define-fun-rec
  last
  ((x list) (y list4)) list
  (match y
    ((nil3 x)
     ((cons3 z ys) (last z ys)))))
(define-fun-rec
  dodeca6
  ((x Int) (y list5)) list3
  (match y
    ((nil5 nil2)
     ((cons5 z x2)
      (cons2 (pair22 (+ (+ (+ x x) x) z) (+ (+ (+ x x) x) (+ 1 z)))
        (dodeca6 x x2))))))
(define-fun-rec
  dodeca5
  ((x Int) (y list5)) list3
  (match y
    ((nil5 nil2)
     ((cons5 z x2)
      (cons2 (pair22 (+ (+ x x) z) (+ (+ (+ x x) x) z))
        (dodeca5 x x2))))))
(define-fun-rec
  dodeca4
  ((x Int) (y list5)) list3
  (match y
    ((nil5 nil2)
     ((cons5 z x2)
      (cons2 (pair22 (+ x (+ 1 z)) (+ (+ x x) z)) (dodeca4 x x2))))))
(define-fun-rec
  dodeca3
  ((x Int) (y list5)) list3
  (match y
    ((nil5 nil2)
     ((cons5 z x2)
      (cons2 (pair22 (+ x z) (+ (+ x x) z)) (dodeca3 x x2))))))
(define-fun-rec
  dodeca2
  ((x Int) (y list5)) list3
  (match y
    ((nil5 nil2)
     ((cons5 z x2) (cons2 (pair22 z (+ x z)) (dodeca2 x x2))))))
(define-fun-rec
  dodeca
  ((x list5)) list3
  (match x
    ((nil5 nil2)
     ((cons5 y z) (cons2 (pair22 y (+ 1 y)) (dodeca z))))))
(define-fun-rec
  bin
  ((x Int)) list
  (ite
    (= x 0) nil4
    (ite
      (= (mod x 2) 0) (cons4 O (bin (div x 2)))
      (cons4 I (bin (div x 2))))))
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
    ((nil4
      (match y
        ((nil4 true)
         ((cons4 z x2) false))))
     ((cons4 x3 xs)
      (match x3
        ((I
          (match y
            ((nil4 false)
             ((cons4 x4 ys)
              (match x4
                ((I (beq xs ys))
                 (O false)))))))
         (O
          (match y
            ((nil4 false)
             ((cons4 x5 zs)
              (match x5
                ((I false)
                 (O (beq xs zs))))))))))))))
(define-fun-rec
  bpath
  ((x list) (y list) (z list2)) list6
  (match z
    ((nil nil6)
     ((cons x2 x3)
      (match x2
        (((pair2 u v)
          (cons6 (or (and (beq u x) (beq v y)) (and (beq u y) (beq v x)))
            (bpath x y x3)))))))))
(define-fun-rec
  bpath2
  ((x list4) (y list2)) Bool
  (match x
    ((nil3 true)
     ((cons3 z x2)
      (match x2
        ((nil3 true)
         ((cons3 y2 xs)
          (and (or2 (bpath z y2 y)) (bpath2 (cons3 y2 xs) y)))))))))
(define-fun-rec
  belem
  ((x list) (y list4)) list6
  (match y
    ((nil3 nil6)
     ((cons3 z x2) (cons6 (beq x z) (belem x x2))))))
(define-fun
  belem2
  ((x list) (y list4)) Bool (or2 (belem x y)))
(define-fun-rec
  bunique
  ((x list4)) Bool
  (match x
    ((nil3 true)
     ((cons3 y xs) (and (not (belem2 y xs)) (bunique xs))))))
(define-fun
  btour
  ((x list4) (y list3)) Bool
  (match x
    ((nil3
      (match y
        ((nil2 true)
         ((cons2 z x2) false))))
     ((cons3 x3 x4)
      (match y
        ((nil2 false)
         ((cons2 x5 vs)
          (match x5
            (((pair22 u v)
              (and (beq x3 (last x3 x4))
                (and (bpath2 (cons3 x3 x4) (bgraph (cons2 (pair22 u v) vs)))
                  (and (bunique x4)
                    (= (length (cons3 x3 x4))
                      (ite
                        (<= u v) (+ 1 (+ 1 (maximum-maximum1 v vs)))
                        (+ 1 (+ 1 (maximum-maximum1 u vs))))))))))))))))))
(define-fun-rec
  ++
  ((x list3) (y list3)) list3
  (match x
    ((nil2 y)
     ((cons2 z xs) (cons2 z (++ xs y))))))
(define-fun
  dodeca7
  ((x Int)) list3
  (ite
    (= x 0) nil2
    (++ (cons2 (pair22 (- x 1) 0) (dodeca (primEnumFromTo 0 (- x 1))))
      (++ (dodeca2 x (primEnumFromTo 0 x))
        (++ (dodeca3 x (primEnumFromTo 0 x))
          (++
            (cons2 (pair22 x (+ (+ x x) (- x 1)))
              (dodeca4 x (primEnumFromTo 0 (- x 1))))
            (++ (dodeca5 x (primEnumFromTo 0 x))
              (cons2 (pair22 (+ (+ (+ x x) x) (- x 1)) (+ (+ x x) x))
                (dodeca6 x (primEnumFromTo 0 (- x 1)))))))))))
(assert
  (not
    (forall ((p list4))
      (not
        (btour p
          (++ (cons2 (pair22 (- 3 1) 0) (dodeca (primEnumFromTo 0 (- 3 1))))
            (++ (dodeca2 3 (primEnumFromTo 0 3))
              (++ (dodeca3 3 (primEnumFromTo 0 3))
                (++
                  (cons2 (pair22 3 (+ (+ 3 3) (- 3 1)))
                    (dodeca4 3 (primEnumFromTo 0 (- 3 1))))
                  (++ (dodeca5 3 (primEnumFromTo 0 3))
                    (cons2 (pair22 (+ (+ (+ 3 3) 3) (- 3 1)) (+ (+ 3 3) 3))
                      (dodeca6 3 (primEnumFromTo 0 (- 3 1))))))))))))))
(check-sat)
