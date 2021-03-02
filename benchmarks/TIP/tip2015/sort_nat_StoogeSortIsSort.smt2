(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(define-fun-rec
  take
  ((x Nat) (y list)) list
  (match x
    ((zero nil)
     ((succ z)
      (match y
        ((nil nil)
         ((cons z2 xs) (cons z2 (take z xs)))))))))
(define-fun-rec
  plus
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero y)
     ((succ z) (succ (plus z y))))))
(define-fun-rec
  minus
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero zero)
     ((succ z)
      (match y
        ((zero zero)
         ((succ y2) (minus z y2))))))))
(define-fun-rec
  lt
  ((x Nat) (y Nat)) Bool
  (match y
    ((zero false)
     ((succ z)
      (match x
        ((zero true)
         ((succ n) (lt n z))))))))
(define-fun-rec
  leq
  ((x Nat) (y Nat)) Bool
  (match x
    ((zero true)
     ((succ z)
      (match y
        ((zero false)
         ((succ x2) (leq z x2))))))))
(define-fun
  sort2
  ((x Nat) (y Nat)) list
  (ite (leq x y) (cons x (cons y nil)) (cons y (cons x nil))))
(define-fun-rec
  length
  ((x list)) Nat
  (match x
    ((nil zero)
     ((cons y l) (plus (succ zero) (length l))))))
(define-fun-rec
  insert2
  ((x Nat) (y list)) list
  (match y
    ((nil (cons x nil))
     ((cons z xs)
      (ite (leq x z) (cons x (cons z xs)) (cons z (insert2 x xs)))))))
(define-fun-rec
  isort
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y xs) (insert2 y (isort xs))))))
(define-fun-rec
  idiv
  ((x Nat) (y Nat)) Nat
  (ite (lt x y) zero (succ (idiv (minus x y) y))))
(define-fun-rec
  drop
  ((x Nat) (y list)) list
  (match x
    ((zero y)
     ((succ z)
      (match y
        ((nil nil)
         ((cons z2 xs1) (drop z xs1))))))))
(define-fun
  splitAt
  ((x Nat) (y list)) pair (pair2 (take x y) (drop x y)))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  reverse
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y xs) (++ (reverse xs) (cons y nil))))))
(define-funs-rec
  ((stooge1sort2
    ((x list)) list)
   (stoogesort
    ((x list)) list)
   (stooge1sort1
    ((x list)) list))
  ((match
     (splitAt (idiv (length x) (succ (succ (succ zero)))) (reverse x))
     (((pair2 ys1 zs1) (++ (stoogesort zs1) (reverse ys1)))))
   (match x
     ((nil nil)
      ((cons y z)
       (match z
         ((nil (cons y nil))
          ((cons y2 x2)
           (match x2
             ((nil (sort2 y y2))
              ((cons x3 x4)
               (stooge1sort2
                 (stooge1sort1
                   (stooge1sort2 (cons y (cons y2 (cons x3 x4)))))))))))))))
   (match (splitAt (idiv (length x) (succ (succ (succ zero)))) x)
     (((pair2 ys1 zs) (++ ys1 (stoogesort zs)))))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (not (forall ((xs list)) (= (stoogesort xs) (isort xs)))))
(check-sat)
