(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((zero) (succ (p Nat))))
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
  length
  ((x list)) Nat
  (match x
    ((nil zero)
     ((cons y l) (plus (succ zero) (length l))))))
(define-fun-rec
  go
  ((x Nat) (y Nat) (z Nat)) Nat
  (match z
    ((zero zero)
     ((succ x2)
      (match x
        ((zero
          (match y
            ((zero zero)
             ((succ x5) (minus (succ x2) (succ x5))))))
         ((succ x3)
          (match y
            ((zero (go x3 x2 (succ x2)))
             ((succ x4) (go x3 x4 (succ x2))))))))))))
(define-fun
  mod_structural
  ((x Nat) (y Nat)) Nat (go x zero y))
(define-fun-rec
  drop
  ((x Nat) (y list)) list
  (match x
    ((zero y)
     ((succ z)
      (match y
        ((nil nil)
         ((cons z2 xs1) (drop z xs1))))))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  rotate
  ((x Nat) (y list)) list
  (match x
    ((zero y)
     ((succ z)
      (match y
        ((nil nil)
         ((cons z2 xs1) (rotate z (++ xs1 (cons z2 nil))))))))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert
  (not
    (forall ((n Nat) (xs list))
      (= (rotate n xs)
        (++ (drop (mod_structural n (length xs)) xs)
          (take (mod_structural n (length xs)) xs))))))
(check-sat)
