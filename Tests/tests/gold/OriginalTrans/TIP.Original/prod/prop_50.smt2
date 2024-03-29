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
(assert (forall ((x_43 Nat_0))
	(projS_1 x_43 (S_0 x_43))))
(assert (isZ_2 Z_0))
(assert (forall ((x_45 Nat_0))
	(isS_0 (S_0 x_45))))
(assert (forall ((x_46 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_46))))
(assert (forall ((x_47 Nat_0))
	(diseqNat_0 (S_0 x_47) Z_0)))
(assert (forall ((x_48 Nat_0) (x_49 Nat_0))
	(=> (diseqNat_0 x_48 x_49)
	    (diseqNat_0 (S_0 x_48) (S_0 x_49)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_51 Nat_0) (x_52 list_0))
	(head_1 x_51 (cons_0 x_51 x_52))))
(assert (forall ((x_51 Nat_0) (x_52 list_0))
	(tail_1 x_52 (cons_0 x_51 x_52))))
(assert (isnil_0 nil_0))
(assert (forall ((x_54 Nat_0) (x_55 list_0))
	(iscons_0 (cons_0 x_54 x_55))))
(assert (forall ((x_56 Nat_0) (x_57 list_0))
	(diseqlist_0 nil_0 (cons_0 x_56 x_57))))
(assert (forall ((x_58 Nat_0) (x_59 list_0))
	(diseqlist_0 (cons_0 x_58 x_59) nil_0)))
(assert (forall ((x_60 Nat_0) (x_61 list_0) (x_62 Nat_0) (x_63 list_0))
	(=> (diseqNat_0 x_60 x_62)
	    (diseqlist_0 (cons_0 x_60 x_61) (cons_0 x_62 x_63)))))
(assert (forall ((x_60 Nat_0) (x_61 list_0) (x_62 Nat_0) (x_63 list_0))
	(=> (diseqlist_0 x_61 x_63)
	    (diseqlist_0 (cons_0 x_60 x_61) (cons_0 x_62 x_63)))))
(declare-fun x_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_10 Bool_0) (y_1 Nat_0) (x_2 Nat_0))
	(=> (x_0 x_10 x_2 y_1)
	    (x_0 x_10 (S_0 x_2) (S_0 y_1)))))
(assert (forall ((x_2 Nat_0))
	(x_0 false_0 (S_0 x_2) Z_0)))
(assert (forall ((z_1 Nat_0))
	(x_0 false_0 Z_0 (S_0 z_1))))
(assert (x_0 true_0 Z_0 Z_0))
(declare-fun count_0 (Nat_0 Nat_0 list_0) Bool)
(assert (forall ((x_17 Nat_0) (z_2 Nat_0) (xs_0 list_0) (x_3 Nat_0))
	(=>	(and (count_0 x_17 x_3 xs_0)
			(x_0 true_0 x_3 z_2))
		(count_0 (S_0 x_17) x_3 (cons_0 z_2 xs_0)))))
(assert (forall ((x_19 Nat_0) (x_18 Bool_0) (z_2 Nat_0) (xs_0 list_0) (x_3 Nat_0))
	(=>	(and (diseqBool_0 x_18 true_0)
			(count_0 x_19 x_3 xs_0)
			(x_0 x_18 x_3 z_2))
		(count_0 x_19 x_3 (cons_0 z_2 xs_0)))))
(assert (forall ((x_3 Nat_0))
	(count_0 Z_0 x_3 nil_0)))
(declare-fun x_4 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_22 Bool_0) (x_6 Nat_0) (z_3 Nat_0))
	(=> (x_4 x_22 z_3 x_6)
	    (x_4 x_22 (S_0 z_3) (S_0 x_6)))))
(assert (forall ((z_3 Nat_0))
	(x_4 false_0 (S_0 z_3) Z_0)))
(assert (forall ((y_3 Nat_0))
	(x_4 true_0 Z_0 y_3)))
(declare-fun insert_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((z_4 Nat_0) (xs_1 list_0) (x_7 Nat_0))
	(=> (x_4 true_0 x_7 z_4)
	    (insert_0 (cons_0 x_7 (cons_0 z_4 xs_1)) x_7 (cons_0 z_4 xs_1)))))
(assert (forall ((x_30 list_0) (x_28 Bool_0) (z_4 Nat_0) (xs_1 list_0) (x_7 Nat_0))
	(=>	(and (diseqBool_0 x_28 true_0)
			(insert_0 x_30 x_7 xs_1)
			(x_4 x_28 x_7 z_4))
		(insert_0 (cons_0 z_4 x_30) x_7 (cons_0 z_4 xs_1)))))
(assert (forall ((x_7 Nat_0))
	(insert_0 (cons_0 x_7 nil_0) x_7 nil_0)))
(declare-fun isort_0 (list_0 list_0) Bool)
(assert (forall ((x_32 list_0) (x_33 list_0) (y_5 Nat_0) (xs_2 list_0))
	(=>	(and (isort_0 x_33 xs_2)
			(insert_0 x_32 y_5 x_33))
		(isort_0 x_32 (cons_0 y_5 xs_2)))))
(assert (isort_0 nil_0 nil_0))
(assert (forall ((x_36 list_0) (x_37 Nat_0) (x_38 Nat_0) (x_9 Nat_0) (y_6 list_0))
	(=>	(and (diseqNat_0 x_37 x_38)
			(isort_0 x_36 y_6)
			(count_0 x_37 x_9 x_36)
			(count_0 x_38 x_9 y_6))
		false)))
(check-sat)
