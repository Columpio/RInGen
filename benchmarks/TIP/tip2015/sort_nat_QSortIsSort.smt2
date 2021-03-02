(declare-sort fun1 0)
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun lam (Nat) fun1)
(declare-fun lam2 (Nat) fun1)
(declare-fun apply1 (fun1 Nat) Bool)
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
(define-fun
  gt
  ((x Nat) (y Nat)) Bool (lt y x))
(define-fun-rec
  filter
  ((q fun1) (x list)) list
  (match x
    ((nil nil)
     ((cons y xs)
      (ite (apply1 q y) (cons y (filter q xs)) (filter q xs))))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  qsort
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y xs)
      (++ (qsort (filter (lam y) xs))
        (++ (cons y nil) (qsort (filter (lam2 y) xs))))))))
(assert
  (forall ((y Nat) (z Nat)) (= (apply1 (lam y) z) (leq z y))))
(assert
  (forall ((y Nat) (x2 Nat)) (= (apply1 (lam2 y) x2) (gt x2 y))))
(assert (not (forall ((xs list)) (= (qsort xs) (isort xs)))))
(check-sat)
