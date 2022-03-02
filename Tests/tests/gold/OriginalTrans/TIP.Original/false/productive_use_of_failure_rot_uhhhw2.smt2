(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((S_0 (projS_0 Nat_0)) (Z_0 ))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(assert (forall ((x_7 Nat_0))
	(projS_1 x_7 (S_0 x_7))))
(assert (forall ((x_10 Nat_0))
	(isS_0 (S_0 x_10))))
(assert (isZ_2 Z_0))
(assert (forall ((x_11 Nat_0))
	(diseqNat_0 (S_0 x_11) Z_0)))
(assert (forall ((x_12 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_12))))
(assert (forall ((x_13 Nat_0) (x_14 Nat_0))
	(=> (diseqNat_0 x_13 x_14)
	    (diseqNat_0 (S_0 x_13) (S_0 x_14)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_16 Nat_0) (x_17 list_0))
	(head_1 x_16 (cons_0 x_16 x_17))))
(assert (forall ((x_16 Nat_0) (x_17 list_0))
	(tail_1 x_17 (cons_0 x_16 x_17))))
(assert (isnil_0 nil_0))
(assert (forall ((x_19 Nat_0) (x_20 list_0))
	(iscons_0 (cons_0 x_19 x_20))))
(assert (forall ((x_21 Nat_0) (x_22 list_0))
	(diseqlist_0 nil_0 (cons_0 x_21 x_22))))
(assert (forall ((x_23 Nat_0) (x_24 list_0))
	(diseqlist_0 (cons_0 x_23 x_24) nil_0)))
(assert (forall ((x_25 Nat_0) (x_26 list_0) (x_27 Nat_0) (x_28 list_0))
	(=> (diseqNat_0 x_25 x_27)
	    (diseqlist_0 (cons_0 x_25 x_26) (cons_0 x_27 x_28)))))
(assert (forall ((x_25 Nat_0) (x_26 list_0) (x_27 Nat_0) (x_28 list_0))
	(=> (diseqlist_0 x_26 x_28)
	    (diseqlist_0 (cons_0 x_25 x_26) (cons_0 x_27 x_28)))))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_2 Nat_0) (y_0 Nat_0) (xs_0 list_0))
	(=> (length_0 x_2 xs_0)
	    (length_0 (S_0 x_2) (cons_0 y_0 xs_0)))))
(assert (length_0 Z_0 nil_0))
(assert (forall ((x_4 Nat_0) (xs_1 list_0) (ys_0 list_0))
	(=>	(and (diseqlist_0 xs_1 ys_0)
			(length_0 x_4 xs_1)
			(length_0 x_4 ys_0))
		false)))
(check-sat)