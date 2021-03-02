(declare-sort fun1 0)
(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  Expr
  ((Var (proj1-Var Int)) (Lam (proj1-Lam Int) (proj2-Lam Expr))
   (App (proj1-App Expr) (proj2-App Expr))))
(declare-fun lam (Int) fun1)
(declare-fun apply1 (fun1 Int) Bool)
(define-fun-rec
  new-maximum
  ((x Int) (y list)) Int
  (match y
    ((nil x)
     ((cons z ys)
      (ite (<= x z) (new-maximum z ys) (new-maximum x ys))))))
(define-fun
  new
  ((x list)) Int (+ (new-maximum 0 x) 1))
(define-fun-rec
  filter
  ((p fun1) (x list)) list
  (match x
    ((nil nil)
     ((cons y xs)
      (ite (apply1 p y) (cons y (filter p xs)) (filter p xs))))))
(define-fun-rec
  elem
  ((x Int) (y list)) Bool
  (match y
    ((nil false)
     ((cons z xs) (or (= z x) (elem x xs))))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  free
  ((x Expr)) list
  (match x
    (((Var y) (cons y nil))
     ((Lam z b) (filter (lam z) (free b)))
     ((App a2 b2) (++ (free a2) (free b2))))))
(define-fun-rec
  subst
  ((x Int) (y Expr) (z Expr)) Expr
  (match z
    (((Var y2) (ite (= x y2) y (Var y2)))
     ((Lam y3 a)
      (let ((z2 (new (++ (free y) (free a)))))
        (ite
          (= x y3) (Lam y3 a)
          (ite
            (elem y3 (free y)) (subst x y (Lam z2 (subst y3 (Var z2) a)))
            (Lam y3 (subst x y a))))))
     ((App a2 b2) (App (subst x y a2) (subst x y b2))))))
(assert
  (forall ((z Int) (x2 Int))
    (= (apply1 (lam z) x2) (distinct z x2))))
(assert
  (not
    (forall ((x Int) (e Expr) (a Expr) (y Int))
      (=> (not (elem x (free a)))
        (= (elem y (free a)) (elem y (free (subst x e a))))))))
(check-sat)
