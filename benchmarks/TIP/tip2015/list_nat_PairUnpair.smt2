(declare-sort sk 0)
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(define-fun-rec
  unpair
  ((x list)) list2
  (match x
    ((nil nil2)
     ((cons y xys)
      (match y (((pair2 z y2) (cons2 z (cons2 y2 (unpair xys))))))))))
(define-fun-rec
  plus
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero y)
     ((succ z) (succ (plus z y))))))
(define-fun-rec
  pairs
  ((x list2)) list
  (match x
    ((nil2 nil)
     ((cons2 y z)
      (match z
        ((nil2 nil)
         ((cons2 y2 xs) (cons (pair2 y y2) (pairs xs)))))))))
(define-fun-rec
  length
  ((x list2)) Nat
  (match x
    ((nil2 zero)
     ((cons2 y l) (plus (succ zero) (length l))))))
(define-fun-rec
  even
  ((x Nat)) Bool
  (match x
    ((zero true)
     ((succ y) (not (even y))))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert
  (not
    (forall ((xs list2))
      (=> (= (ite (even (length xs)) zero (succ zero)) zero)
        (= (unpair (pairs xs)) xs)))))
(check-sat)
