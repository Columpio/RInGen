(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-sort fun14 0)
(declare-datatype
  pair3 ((pair22 (proj1-pair2 sk) (proj2-pair2 sk))))
(declare-datatype list ((nil3) (cons3 (head3 sk) (tail3 list))))
(declare-datatype
  list3 ((nil2) (cons2 (head2 list) (tail2 list3))))
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair list))))
(declare-datatype list2 ((nil) (cons (head pair) (tail list2))))
(declare-fun lam (sk) fun13)
(declare-const lam2 fun12)
(declare-fun lam3 (list) fun14)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) fun13)
(declare-fun apply13 (fun13 sk) Bool)
(declare-fun apply14 (fun14 list) Bool)
(define-fun-rec
  select2
  ((x sk) (y list2)) list2
  (match y
    ((nil nil)
     ((cons z x2)
      (match z
        (((pair2 y2 ys)
          (cons (pair2 y2 (cons3 x ys)) (select2 x x2)))))))))
(define-fun-rec
  select22
  ((x list)) list2
  (match x
    ((nil3 nil)
     ((cons3 y xs) (cons (pair2 y xs) (select2 y (select22 xs)))))))
(define-fun-rec
  formula
  ((x list2)) list3
  (match x
    ((nil nil2)
     ((cons y z)
      (match y (((pair2 y2 ys) (cons2 (cons3 y2 ys) (formula z)))))))))
(define-fun-rec
  elem
  ((x sk) (y list)) Bool
  (match y
    ((nil3 false)
     ((cons3 z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  deleteBy
  ((x fun12) (y sk) (z list)) list
  (match z
    ((nil3 nil3)
     ((cons3 y2 ys)
      (ite
        (apply13 (apply12 x y) y2) ys (cons3 y2 (deleteBy x y ys)))))))
(define-fun-rec
  isPermutation
  ((x list) (y list)) Bool
  (match x
    ((nil3
      (match y
        ((nil3 true)
         ((cons3 z x2) false))))
     ((cons3 x3 xs)
      (and (elem x3 y) (isPermutation xs (deleteBy lam2 x3 y)))))))
(define-fun-rec
  all2
  ((p fun13) (x list)) Bool
  (match x
    ((nil3 true)
     ((cons3 y xs) (and (apply13 p y) (all2 p xs))))))
(define-fun-rec
  all
  ((p fun14) (x list3)) Bool
  (match x
    ((nil2 true)
     ((cons2 y xs) (and (apply14 p y) (all p xs))))))
(assert (forall ((x4 sk)) (= (apply12 lam2 x4) (lam x4))))
(assert
  (forall ((x4 sk) (x5 sk)) (= (apply13 (lam x4) x5) (= x4 x5))))
(assert
  (forall ((xs list) (x list))
    (= (apply14 (lam3 xs) x) (isPermutation x xs))))
(assert
  (not (forall ((xs list)) (all (lam3 xs) (formula (select22 xs))))))
(check-sat)
