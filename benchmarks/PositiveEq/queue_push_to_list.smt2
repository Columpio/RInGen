(set-logic HORN)

(declare-datatype Nat ((Z) (S (nextnat Nat))))
(declare-datatype Tree ((leaf) (node (trn1 Nat) (ltree Tree) (rtree Tree))))
(declare-datatype Lst ((nil) (cons (head Nat) (tail Lst))))
(declare-datatype Queue ((queue (front Lst) (back Lst))))

(declare-fun add (Nat Nat Nat) Bool)
(declare-fun lt (Nat Nat) Bool)
(declare-fun le (Nat Nat) Bool)
(assert (forall ((y Nat)) (add Z y y)))
(assert (forall ((x Nat) (y Nat) (z Nat)) (=> (add x y z) (add (S x) y (S z)))))
(assert (forall ((y Nat)) (lt Z (S y))))
(assert (forall ((x Nat) (y Nat)) (=> (lt x y) (lt (S x) (S y)))))
(assert (forall ((x Nat) (y Nat)) (=> (or (lt x y) (= x y)) (le x y))))

(declare-fun len (Lst Nat) Bool)
(assert (len nil Z))
(assert (forall ((x Nat) (y Lst) (l Nat)) (=> (len y l) (len (cons x y) (S l)))))
(declare-fun qlen (Queue Nat) Bool)
(assert (forall ((x Lst) (y Lst) (xs Nat) (ys Nat) (s Nat)) (=> (and (len x xs) (len y ys) (add xs ys s)) (qlen (queue x y) s))))
(declare-fun append (Lst Lst Lst) Bool)
(assert (forall ((y Lst)) (append nil y y)))
(assert (forall ((c Nat) (x Lst) (y Lst) (z Lst)) (=> (append x y z) (append (cons c x) y (cons c z)))))
(declare-fun rev2 (Lst Lst Lst) Bool)
(assert (forall ((a Lst)) (rev2 nil a a)))
(assert (forall ((x Nat) (t Lst) (a Lst) (l Lst)) (=> (rev2 t (cons x a) l) (rev2 (cons x t) a l))))
(declare-fun qrev (Lst Lst) Bool)
(assert (forall ((x Lst) (y Lst)) (=> (rev2 x nil y) (qrev x y))))
(declare-fun amortizeQueue (Lst Lst Queue) Bool)
(assert (forall ((x Lst) (y Lst) (xl Nat) (yl Nat)) (=> (and (len x xl) (len y yl) (le yl xl)) (amortizeQueue x y (queue x y)))))
(assert (forall ((x Lst) (y Lst) (xl Nat) (yl Nat) (yr Lst) (xy Lst)) (=> (and (len x xl) (len y yl) (lt xl yl) (qrev y yr) (append x yr xy)) (amortizeQueue x y (queue xy nil)))))
(declare-fun qpush (Queue Nat Queue) Bool)
(assert (forall ((x Lst) (y Lst) (n Nat) (q Queue)) (=> (amortizeQueue x (cons n y) q) (qpush (queue x y) n q))))
(declare-fun queue-to-lst (Queue Lst) Bool)
(assert (forall ((x Lst) (y Lst) (yr Lst) (xy Lst)) (=> (and (qrev y yr) (append x yr xy)) (queue-to-lst (queue x y) xy))))

;(assert (forall ((x Lst) (y Lst) (z Lst)) (=> (and (append x y xy) (append xy z xyz1) (append y z yz) (append x yz xyz2)) (= xyz1 xyz2))))

; extra lemmas
;(assert (forall ((x Lst) (y Lst) (z Lst)) (= (append (append x y) z) (append x (append y z)))))
;(assert (forall ((x Lst) (a Lst)) (= (rev2 x a) (append (rev2 x nil) a))))

(assert (forall ((q Queue) (n Nat) (ql Lst) (qln Lst) (qn Queue) (qnl Lst) (l1 Nat) (l2 Nat))
	(=> (and (queue-to-lst q ql) (append ql (cons n nil) qln) (qpush q n qn) (queue-to-lst qn qnl) (len qln l1) (len qnl l2) (= (S l1) l2)) false)))

;(assert (not (forall ((q Queue) (n Nat)) (= (append (queue-to-lst q) (cons n nil)) (queue-to-lst (qpush q n))))))

(check-sat)

