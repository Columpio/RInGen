(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_14 Nat_0))
	(projS_1 x_14 (S_0 x_14))))
(assert (isZ_2 Z_0))
(assert (forall ((x_16 Nat_0))
	(isS_0 (S_0 x_16))))
(assert (forall ((x_17 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_17))))
(assert (forall ((x_18 Nat_0))
	(diseqNat_0 (S_0 x_18) Z_0)))
(assert (forall ((x_19 Nat_0) (x_20 Nat_0))
	(=> (diseqNat_0 x_19 x_20)
	    (diseqNat_0 (S_0 x_19) (S_0 x_20)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_22 Nat_0) (x_23 list_0))
	(head_1 x_22 (cons_0 x_22 x_23))))
(assert (forall ((x_22 Nat_0) (x_23 list_0))
	(tail_1 x_23 (cons_0 x_22 x_23))))
(assert (isnil_0 nil_0))
(assert (forall ((x_25 Nat_0) (x_26 list_0))
	(iscons_0 (cons_0 x_25 x_26))))
(assert (forall ((x_27 Nat_0) (x_28 list_0))
	(diseqlist_0 nil_0 (cons_0 x_27 x_28))))
(assert (forall ((x_29 Nat_0) (x_30 list_0))
	(diseqlist_0 (cons_0 x_29 x_30) nil_0)))
(assert (forall ((x_31 Nat_0) (x_32 list_0) (x_33 Nat_0) (x_34 list_0))
	(=> (diseqNat_0 x_31 x_33)
	    (diseqlist_0 (cons_0 x_31 x_32) (cons_0 x_33 x_34)))))
(assert (forall ((x_31 Nat_0) (x_32 list_0) (x_33 Nat_0) (x_34 list_0))
	(=> (diseqlist_0 x_32 x_34)
	    (diseqlist_0 (cons_0 x_31 x_32) (cons_0 x_33 x_34)))))
(declare-fun last_0 (Nat_0 list_0) Bool)
(assert (forall ((x_4 Nat_0) (x_1 Nat_0) (x_2 list_0) (y_0 Nat_0))
	(=> (last_0 x_4 (cons_0 x_1 x_2))
	    (last_0 x_4 (cons_0 y_0 (cons_0 x_1 x_2))))))
(assert (forall ((x_6 Nat_0))
	(last_0 x_6 (cons_0 x_6 nil_0))))
(assert (last_0 Z_0 nil_0))
(assert (forall ((x_8 Nat_0) (x_9 Nat_0) (y_1 Nat_0) (z_2 list_0) (x_3 Nat_0))
	(=>	(and (diseqNat_0 x_8 x_9)
			true
			(last_0 x_8 (cons_0 x_3 (cons_0 y_1 z_2)))
			(last_0 x_9 (cons_0 y_1 z_2)))
		false)))
(assert (forall ((x_10 Nat_0) (x_11 Nat_0) (x_3 Nat_0))
	(=>	(and (diseqNat_0 x_10 x_11)
			false
			(last_0 x_10 (cons_0 x_3 nil_0))
			(last_0 x_11 nil_0))
		false)))
(check-sat)