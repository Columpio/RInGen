(set-logic HORN)

(declare-datatypes ((Nat 0) (list 0)) (((Z) (S (prev Nat))) ((nil) (cons (car Nat) (cdr list)))))

(declare-fun sublist (list list) Bool)
(assert (forall ((y Nat) (ys list)) (sublist nil (cons y ys))))
(assert (forall ((xs list) (ys list) (x Nat)) (=> (sublist xs ys) (sublist (cons x xs) (cons x ys)))))

(assert (forall ((x list) (y list)) (=> (and (sublist x y) (sublist y x)) false)))

(check-sat)
(get-model)
