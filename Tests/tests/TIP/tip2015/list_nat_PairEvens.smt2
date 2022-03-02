(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-const lam fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 pair) sk)
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
  map3
  ((f fun1) (x list2)) list2
  (match x
    ((nil2 nil2)
     ((cons2 y xs) (cons2 (apply1 f y) (map3 f xs))))))
(define-fun-rec
  map2
  ((f fun12) (x list)) list2
  (match x
    ((nil nil2)
     ((cons y xs) (cons2 (apply12 f y) (map2 f xs))))))
(define-fun-rec
  length
  ((x list2)) Nat
  (match x
    ((nil2 zero)
     ((cons2 y l) (plus (succ zero) (length l))))))
(define-funs-rec
  ((evens
    ((x list2)) list2)
   (odds
    ((x list2)) list2))
  ((match x
     ((nil2 nil2)
      ((cons2 y xs) (cons2 y (odds xs)))))
   (match x
     ((nil2 nil2)
      ((cons2 y xs) (evens xs))))))
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
  (forall ((x pair))
    (= (apply12 lam x) (match x (((pair2 y z) y))))))
(assert
  (not
    (forall ((xs list2))
      (=> (= (ite (even (length xs)) zero (succ zero)) zero)
        (= (map2 lam (pairs xs)) (evens xs))))))
(check-sat)
