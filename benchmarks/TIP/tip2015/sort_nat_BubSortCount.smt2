(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair Bool) (proj2-pair list))))
(define-fun-rec
  plus
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero y)
     ((succ z) (succ (plus z y))))))
(define-fun-rec
  leq
  ((x Nat) (y Nat)) Bool
  (match x
    ((zero true)
     ((succ z)
      (match y
        ((zero false)
         ((succ x2) (leq z x2))))))))
(define-fun-rec
  count
  ((x Nat) (y list)) Nat
  (match y
    ((nil zero)
     ((cons z ys)
      (ite (= x z) (plus (succ zero) (count x ys)) (count x ys))))))
(define-fun-rec
  bubble
  ((x list)) pair
  (match x
    ((nil (pair2 false nil))
     ((cons y z)
      (match z
        ((nil (pair2 false (cons y nil)))
         ((cons y2 xs)
          (ite
            (leq y y2)
            (match (bubble (cons y2 xs))
              (((pair2 b12 ys12) (pair2 b12 (cons y ys12)))))
            (match (bubble (cons y xs))
              (((pair2 b1 ys1) (pair2 true (cons y2 ys1)))))))))))))
(define-fun-rec
  bubsort
  ((x list)) list
  (match (bubble x) (((pair2 c ys1) (ite c (bubsort ys1) x)))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert
  (not
    (forall ((x Nat) (xs list))
      (= (count x (bubsort xs)) (count x xs)))))
(check-sat)
