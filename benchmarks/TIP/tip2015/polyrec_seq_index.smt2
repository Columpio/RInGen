(declare-sort sk 0)
(declare-sort pair4 0)
(declare-sort list3 0)
(declare-sort Maybe3 0)
(declare-sort Seq2 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype
  pair3 ((pair22 (proj1-pair2 sk) (proj2-pair2 sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype Maybe ((Nothing2) (Just2 (proj1-Just2 sk))))
(declare-datatype
  pair ((pair2 (proj1-pair sk) (proj2-pair Maybe))))
(declare-datatype Maybe2 ((Nothing) (Just (proj1-Just pair))))
(declare-datatype
  Seq ((Nil) (Cons (proj1-Cons pair) (proj2-Cons Seq2))))
(declare-datatype
  Seq3 ((Nil2) (Cons2 (proj1-Cons2 sk) (proj2-Cons2 Seq))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(declare-fun pair32 (list) list3)
(declare-fun index (Int Seq) Maybe2)
(declare-fun fromList (list) Seq)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) Maybe)
(define-fun-rec
  pair33
  ((x list2)) list
  (match x
    ((nil2 nil)
     ((cons2 y z)
      (match z
        ((nil2 (cons (pair2 y Nothing2) nil))
         ((cons2 y2 xs) (cons (pair2 y (Just2 y2)) (pair33 xs)))))))))
(define-fun-rec
  lookup
  ((x Int) (y list2)) Maybe
  (match y
    ((nil2 Nothing2)
     ((cons2 z x2) (ite (= x 0) (Just2 z) (lookup (- x 1) x2))))))
(define-fun
  index2
  ((x Int) (y Seq3)) Maybe
  (match y
    ((Nil2 Nothing2)
     ((Cons2 z x2)
      (ite
        (= x 0) (Just2 z)
        (ite
          (= (mod x 2) 0)
          (match (index (div (- x 1) 2) x2)
            ((Nothing Nothing2)
             ((Just x5) (match x5 (((pair2 x6 y3) y3))))))
          (match (index (div (- x 1) 2) x2)
            ((Nothing Nothing2)
             ((Just x3) (match x3 (((pair2 x4 y2) (Just2 x4)))))))))))))
(define-fun
  fromList2
  ((x list2)) Seq3
  (match x
    ((nil2 Nil2)
     ((cons2 y xs) (Cons2 y (fromList (pair33 xs)))))))
(define-fun
  =<<<
  ((x fun12) (y Maybe)) Maybe
  (match y
    ((Nothing2 Nothing2)
     ((Just2 z) (apply12 x z)))))
(define-fun
  <$$>
  ((x fun1) (y Maybe)) Maybe
  (match y
    ((Nothing2 Nothing2)
     ((Just2 z) (Just2 (apply1 x z))))))
(assert
  (not
    (forall ((n Int) (xs list2))
      (=> (>= n 0) (= (lookup n xs) (index2 n (fromList2 xs)))))))
(check-sat)
