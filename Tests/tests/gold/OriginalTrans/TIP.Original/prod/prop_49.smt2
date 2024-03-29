(set-logic HORN)
(declare-datatypes ((Bool_0 0)) (((false_0 ) (true_0 ))))
(declare-fun diseqBool_0 (Bool_0 Bool_0) Bool)
(declare-fun isfalse_1 (Bool_0) Bool)
(declare-fun istrue_1 (Bool_0) Bool)
(assert (isfalse_1 false_0))
(assert (istrue_1 true_0))
(assert (diseqBool_0 false_0 true_0))
(assert (diseqBool_0 true_0 false_0))
(declare-fun and_0 (Bool_0 Bool_0 Bool_0) Bool)
(declare-fun or_0 (Bool_0 Bool_0 Bool_0) Bool)
(declare-fun hence_0 (Bool_0 Bool_0 Bool_0) Bool)
(declare-fun not_0 (Bool_0 Bool_0) Bool)
(assert (and_0 false_0 false_0 false_0))
(assert (and_0 false_0 true_0 false_0))
(assert (and_0 false_0 false_0 true_0))
(assert (and_0 true_0 true_0 true_0))
(assert (or_0 false_0 false_0 false_0))
(assert (or_0 true_0 true_0 false_0))
(assert (or_0 true_0 false_0 true_0))
(assert (or_0 true_0 true_0 true_0))
(assert (hence_0 true_0 false_0 false_0))
(assert (hence_0 false_0 true_0 false_0))
(assert (hence_0 true_0 false_0 true_0))
(assert (hence_0 true_0 true_0 true_0))
(assert (not_0 true_0 false_0))
(assert (not_0 false_0 true_0))
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_44 Nat_0))
	(projS_1 x_44 (S_0 x_44))))
(assert (isZ_2 Z_0))
(assert (forall ((x_46 Nat_0))
	(isS_0 (S_0 x_46))))
(assert (forall ((x_47 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_47))))
(assert (forall ((x_48 Nat_0))
	(diseqNat_0 (S_0 x_48) Z_0)))
(assert (forall ((x_49 Nat_0) (x_50 Nat_0))
	(=> (diseqNat_0 x_49 x_50)
	    (diseqNat_0 (S_0 x_49) (S_0 x_50)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_52 Nat_0) (x_53 list_0))
	(head_1 x_52 (cons_0 x_52 x_53))))
(assert (forall ((x_52 Nat_0) (x_53 list_0))
	(tail_1 x_53 (cons_0 x_52 x_53))))
(assert (isnil_0 nil_0))
(assert (forall ((x_55 Nat_0) (x_56 list_0))
	(iscons_0 (cons_0 x_55 x_56))))
(assert (forall ((x_57 Nat_0) (x_58 list_0))
	(diseqlist_0 nil_0 (cons_0 x_57 x_58))))
(assert (forall ((x_59 Nat_0) (x_60 list_0))
	(diseqlist_0 (cons_0 x_59 x_60) nil_0)))
(assert (forall ((x_61 Nat_0) (x_62 list_0) (x_63 Nat_0) (x_64 list_0))
	(=> (diseqNat_0 x_61 x_63)
	    (diseqlist_0 (cons_0 x_61 x_62) (cons_0 x_63 x_64)))))
(assert (forall ((x_61 Nat_0) (x_62 list_0) (x_63 Nat_0) (x_64 list_0))
	(=> (diseqlist_0 x_62 x_64)
	    (diseqlist_0 (cons_0 x_61 x_62) (cons_0 x_63 x_64)))))
(declare-fun barbar_0 (Bool_0 Bool_0 Bool_0) Bool)
(assert (forall ((y_0 Bool_0))
	(barbar_0 true_0 true_0 y_0)))
(assert (forall ((x_12 Bool_0) (x_0 Bool_0))
	(=> (diseqBool_0 x_0 true_0)
	    (barbar_0 x_12 x_0 x_12))))
(declare-fun x_1 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_13 Bool_0) (y_2 Nat_0) (x_3 Nat_0))
	(=> (x_1 x_13 x_3 y_2)
	    (x_1 x_13 (S_0 x_3) (S_0 y_2)))))
(assert (forall ((x_3 Nat_0))
	(x_1 false_0 (S_0 x_3) Z_0)))
(assert (forall ((z_1 Nat_0))
	(x_1 false_0 Z_0 (S_0 z_1))))
(assert (x_1 true_0 Z_0 Z_0))
(declare-fun elem_0 (Bool_0 Nat_0 list_0) Bool)
(assert (forall ((x_18 Bool_0) (x_19 Bool_0) (x_20 Bool_0) (z_2 Nat_0) (xs_0 list_0) (x_4 Nat_0))
	(=>	(and (x_1 x_19 x_4 z_2)
			(elem_0 x_20 x_4 xs_0)
			(barbar_0 x_18 x_19 x_20))
		(elem_0 x_18 x_4 (cons_0 z_2 xs_0)))))
(assert (forall ((x_4 Nat_0))
	(elem_0 false_0 x_4 nil_0)))
(declare-fun x_5 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_23 Bool_0) (x_7 Nat_0) (z_3 Nat_0))
	(=> (x_5 x_23 z_3 x_7)
	    (x_5 x_23 (S_0 z_3) (S_0 x_7)))))
(assert (forall ((z_3 Nat_0))
	(x_5 false_0 (S_0 z_3) Z_0)))
(assert (forall ((y_4 Nat_0))
	(x_5 true_0 Z_0 y_4)))
(declare-fun insert_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((z_4 Nat_0) (xs_1 list_0) (x_8 Nat_0))
	(=> (x_5 true_0 x_8 z_4)
	    (insert_0 (cons_0 x_8 (cons_0 z_4 xs_1)) x_8 (cons_0 z_4 xs_1)))))
(assert (forall ((x_31 list_0) (x_29 Bool_0) (z_4 Nat_0) (xs_1 list_0) (x_8 Nat_0))
	(=>	(and (diseqBool_0 x_29 true_0)
			(insert_0 x_31 x_8 xs_1)
			(x_5 x_29 x_8 z_4))
		(insert_0 (cons_0 z_4 x_31) x_8 (cons_0 z_4 xs_1)))))
(assert (forall ((x_8 Nat_0))
	(insert_0 (cons_0 x_8 nil_0) x_8 nil_0)))
(declare-fun isort_0 (list_0 list_0) Bool)
(assert (forall ((x_33 list_0) (x_34 list_0) (y_6 Nat_0) (xs_2 list_0))
	(=>	(and (isort_0 x_34 xs_2)
			(insert_0 x_33 y_6 x_34))
		(isort_0 x_33 (cons_0 y_6 xs_2)))))
(assert (isort_0 nil_0 nil_0))
(assert (forall ((x_38 list_0) (x_37 Bool_0) (x_10 Nat_0) (y_7 list_0))
	(=>	(and (diseqBool_0 x_37 true_0)
			(isort_0 x_38 y_7)
			(elem_0 true_0 x_10 x_38)
			(elem_0 x_37 x_10 y_7))
		false)))
(check-sat)
