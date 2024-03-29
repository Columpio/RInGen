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
(assert (forall ((x_36 Nat_0))
	(projS_1 x_36 (S_0 x_36))))
(assert (isZ_2 Z_0))
(assert (forall ((x_38 Nat_0))
	(isS_0 (S_0 x_38))))
(assert (forall ((x_39 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_39))))
(assert (forall ((x_40 Nat_0))
	(diseqNat_0 (S_0 x_40) Z_0)))
(assert (forall ((x_41 Nat_0) (x_42 Nat_0))
	(=> (diseqNat_0 x_41 x_42)
	    (diseqNat_0 (S_0 x_41) (S_0 x_42)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_44 Nat_0) (x_45 list_0))
	(head_1 x_44 (cons_0 x_44 x_45))))
(assert (forall ((x_44 Nat_0) (x_45 list_0))
	(tail_1 x_45 (cons_0 x_44 x_45))))
(assert (isnil_0 nil_0))
(assert (forall ((x_47 Nat_0) (x_48 list_0))
	(iscons_0 (cons_0 x_47 x_48))))
(assert (forall ((x_49 Nat_0) (x_50 list_0))
	(diseqlist_0 nil_0 (cons_0 x_49 x_50))))
(assert (forall ((x_51 Nat_0) (x_52 list_0))
	(diseqlist_0 (cons_0 x_51 x_52) nil_0)))
(assert (forall ((x_53 Nat_0) (x_54 list_0) (x_55 Nat_0) (x_56 list_0))
	(=> (diseqNat_0 x_53 x_55)
	    (diseqlist_0 (cons_0 x_53 x_54) (cons_0 x_55 x_56)))))
(assert (forall ((x_53 Nat_0) (x_54 list_0) (x_55 Nat_0) (x_56 list_0))
	(=> (diseqlist_0 x_54 x_56)
	    (diseqlist_0 (cons_0 x_53 x_54) (cons_0 x_55 x_56)))))
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
(assert (forall ((x_16 Nat_0) (z_2 Nat_0) (ys_0 list_0) (x_3 Nat_0))
	(=>	(and (count_0 x_16 x_3 ys_0)
			(x_0 true_0 x_3 z_2))
		(count_0 (S_0 x_16) x_3 (cons_0 z_2 ys_0)))))
(assert (forall ((x_18 Nat_0) (x_17 Bool_0) (z_2 Nat_0) (ys_0 list_0) (x_3 Nat_0))
	(=>	(and (diseqBool_0 x_17 true_0)
			(count_0 x_18 x_3 ys_0)
			(x_0 x_17 x_3 z_2))
		(count_0 x_18 x_3 (cons_0 z_2 ys_0)))))
(assert (forall ((x_3 Nat_0))
	(count_0 Z_0 x_3 nil_0)))
(declare-fun x_4 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_21 Bool_0) (x_6 Nat_0) (z_3 Nat_0))
	(=> (x_4 x_21 z_3 x_6)
	    (x_4 x_21 (S_0 z_3) (S_0 x_6)))))
(assert (forall ((z_3 Nat_0))
	(x_4 false_0 (S_0 z_3) Z_0)))
(assert (forall ((y_3 Nat_0))
	(x_4 true_0 Z_0 y_3)))
(declare-fun x_7 (list_0 list_0 list_0) Bool)
(assert (forall ((x_26 list_0) (z_4 Nat_0) (xs_0 list_0) (y_4 list_0))
	(=> (x_7 x_26 xs_0 y_4)
	    (x_7 (cons_0 z_4 x_26) (cons_0 z_4 xs_0) y_4))))
(assert (forall ((x_27 list_0))
	(x_7 x_27 nil_0 x_27)))
(assert (forall ((x_28 Nat_0) (x_29 list_0) (x_30 Nat_0) (x_31 Bool_0) (n_0 Nat_0) (xs_1 list_0) (ys_1 list_0))
	(=>	(and (diseqBool_0 x_31 true_0)
			(count_0 x_28 n_0 xs_1)
			(x_7 x_29 xs_1 ys_1)
			(count_0 x_30 n_0 x_29)
			(x_4 x_31 x_28 x_30))
		false)))
(check-sat)
