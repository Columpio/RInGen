(set-logic HORN)


(declare-datatype Nat ((Z) (S (nextnat Nat))))
(declare-datatype Tree ((leaf) (node (trn1 Nat) (ltree Tree) (rtree Tree))))

(declare-fun add (Nat Nat Nat) Bool)
(declare-fun lt (Nat Nat) Bool)
(declare-fun le (Nat Nat) Bool)
(assert (forall ((y Nat)) (add Z y y)))
(assert (forall ((x Nat) (y Nat) (z Nat)) (=> (add x y z) (add (S x) y (S z)))))
(assert (forall ((y Nat)) (lt Z (S y))))
(assert (forall ((x Nat) (y Nat)) (=> (lt x y) (lt (S x) (S y)))))
(assert (forall ((x Nat) (y Nat)) (=> (or (lt x y) (= x y)) (le x y))))

(declare-fun tinsert (Tree Nat Tree) Bool)
(assert (forall ((i Nat)) (tinsert leaf i (node i leaf leaf))))
(assert (forall ((r Tree) (l Tree) (rt Tree) (d Nat) (i Nat)) (=> (and (lt d i) (tinsert r i rt)) (tinsert (node d l r) i (node d l rt)))))
(assert (forall ((r Tree) (l Tree) (lt Tree) (d Nat) (i Nat)) (=> (and (le i d) (tinsert l i lt)) (tinsert (node d l r) i (node d lt r)))))

(declare-fun tsize (Tree Nat) Bool)
(assert (tsize leaf Z))
(assert (forall ((x Nat) (l Tree) (r Tree) (ls Nat) (rs Nat) (ss Nat)) (=> (and (tsize l ls) (tsize r rs) (add ls rs ss)) (tsize (node x l r) (S ss)))))

(assert (forall ((t Tree) (t2 Tree) (n Nat) (ts Nat) (tts Nat)) (=> (and (tsize t ts) (tinsert t n t2) (tsize t2 tts) (= ts tts)) false)))


(check-sat)

