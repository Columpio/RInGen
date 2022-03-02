(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_17 Nat_0))
	(projS_1 x_17 (S_0 x_17))))
(assert (isZ_2 Z_0))
(assert (forall ((x_19 Nat_0))
	(isS_0 (S_0 x_19))))
(assert (forall ((x_20 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_20))))
(assert (forall ((x_21 Nat_0))
	(diseqNat_0 (S_0 x_21) Z_0)))
(assert (forall ((x_22 Nat_0) (x_23 Nat_0))
	(=> (diseqNat_0 x_22 x_23)
	    (diseqNat_0 (S_0 x_22) (S_0 x_23)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_25 Nat_0) (x_26 list_0))
	(head_1 x_25 (cons_0 x_25 x_26))))
(assert (forall ((x_25 Nat_0) (x_26 list_0))
	(tail_1 x_26 (cons_0 x_25 x_26))))
(assert (isnil_0 nil_0))
(assert (forall ((x_28 Nat_0) (x_29 list_0))
	(iscons_0 (cons_0 x_28 x_29))))
(assert (forall ((x_30 Nat_0) (x_31 list_0))
	(diseqlist_0 nil_0 (cons_0 x_30 x_31))))
(assert (forall ((x_32 Nat_0) (x_33 list_0))
	(diseqlist_0 (cons_0 x_32 x_33) nil_0)))
(assert (forall ((x_34 Nat_0) (x_35 list_0) (x_36 Nat_0) (x_37 list_0))
	(=> (diseqNat_0 x_34 x_36)
	    (diseqlist_0 (cons_0 x_34 x_35) (cons_0 x_36 x_37)))))
(assert (forall ((x_34 Nat_0) (x_35 list_0) (x_36 Nat_0) (x_37 list_0))
	(=> (diseqlist_0 x_35 x_37)
	    (diseqlist_0 (cons_0 x_34 x_35) (cons_0 x_36 x_37)))))
(declare-fun last_0 (Nat_0 list_0) Bool)
(assert (forall ((x_6 Nat_0) (x_1 Nat_0) (x_2 list_0) (y_0 Nat_0))
	(=> (last_0 x_6 (cons_0 x_1 x_2))
	    (last_0 x_6 (cons_0 y_0 (cons_0 x_1 x_2))))))
(assert (forall ((x_8 Nat_0))
	(last_0 x_8 (cons_0 x_8 nil_0))))
(assert (last_0 Z_0 nil_0))
(declare-fun x_3 (list_0 list_0 list_0) Bool)
(assert (forall ((x_11 list_0) (z_2 Nat_0) (xs_0 list_0) (y_1 list_0))
	(=> (x_3 x_11 xs_0 y_1)
	    (x_3 (cons_0 z_2 x_11) (cons_0 z_2 xs_0) y_1))))
(assert (forall ((x_12 list_0))
	(x_3 x_12 nil_0 x_12)))
(assert (forall ((x_13 list_0) (x_14 Nat_0) (x_5 Nat_0) (xs_1 list_0))
	(=>	(and (diseqNat_0 x_14 x_5)
			(x_3 x_13 xs_1 (cons_0 x_5 nil_0))
			(last_0 x_14 x_13))
		false)))
(check-sat)