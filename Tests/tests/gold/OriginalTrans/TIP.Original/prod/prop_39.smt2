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
(assert (forall ((x_32 Nat_0))
	(projS_1 x_32 (S_0 x_32))))
(assert (isZ_2 Z_0))
(assert (forall ((x_34 Nat_0))
	(isS_0 (S_0 x_34))))
(assert (forall ((x_35 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_35))))
(assert (forall ((x_36 Nat_0))
	(diseqNat_0 (S_0 x_36) Z_0)))
(assert (forall ((x_37 Nat_0) (x_38 Nat_0))
	(=> (diseqNat_0 x_37 x_38)
	    (diseqNat_0 (S_0 x_37) (S_0 x_38)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_40 Nat_0) (x_41 list_0))
	(head_1 x_40 (cons_0 x_40 x_41))))
(assert (forall ((x_40 Nat_0) (x_41 list_0))
	(tail_1 x_41 (cons_0 x_40 x_41))))
(assert (isnil_0 nil_0))
(assert (forall ((x_43 Nat_0) (x_44 list_0))
	(iscons_0 (cons_0 x_43 x_44))))
(assert (forall ((x_45 Nat_0) (x_46 list_0))
	(diseqlist_0 nil_0 (cons_0 x_45 x_46))))
(assert (forall ((x_47 Nat_0) (x_48 list_0))
	(diseqlist_0 (cons_0 x_47 x_48) nil_0)))
(assert (forall ((x_49 Nat_0) (x_50 list_0) (x_51 Nat_0) (x_52 list_0))
	(=> (diseqNat_0 x_49 x_51)
	    (diseqlist_0 (cons_0 x_49 x_50) (cons_0 x_51 x_52)))))
(assert (forall ((x_49 Nat_0) (x_50 list_0) (x_51 Nat_0) (x_52 list_0))
	(=> (diseqlist_0 x_50 x_52)
	    (diseqlist_0 (cons_0 x_49 x_50) (cons_0 x_51 x_52)))))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_10 list_0) (x_1 Nat_0) (x_2 list_0) (z_1 Nat_0))
	(=> (drop_0 x_10 z_1 x_2)
	    (drop_0 x_10 (S_0 z_1) (cons_0 x_1 x_2)))))
(assert (forall ((z_1 Nat_0))
	(drop_0 nil_0 (S_0 z_1) nil_0)))
(assert (forall ((x_12 list_0))
	(drop_0 x_12 Z_0 x_12)))
(declare-fun barbar_0 (Bool_0 Bool_0 Bool_0) Bool)
(assert (forall ((y_1 Bool_0))
	(barbar_0 true_0 true_0 y_1)))
(assert (forall ((x_14 Bool_0) (x_3 Bool_0))
	(=> (diseqBool_0 x_3 true_0)
	    (barbar_0 x_14 x_3 x_14))))
(declare-fun x_4 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_15 Bool_0) (y_3 Nat_0) (x_6 Nat_0))
	(=> (x_4 x_15 x_6 y_3)
	    (x_4 x_15 (S_0 x_6) (S_0 y_3)))))
(assert (forall ((x_6 Nat_0))
	(x_4 false_0 (S_0 x_6) Z_0)))
(assert (forall ((z_2 Nat_0))
	(x_4 false_0 Z_0 (S_0 z_2))))
(assert (x_4 true_0 Z_0 Z_0))
(declare-fun elem_0 (Bool_0 Nat_0 list_0) Bool)
(assert (forall ((x_20 Bool_0) (x_21 Bool_0) (x_22 Bool_0) (z_3 Nat_0) (xs_0 list_0) (x_7 Nat_0))
	(=>	(and (x_4 x_21 x_7 z_3)
			(elem_0 x_22 x_7 xs_0)
			(barbar_0 x_20 x_21 x_22))
		(elem_0 x_20 x_7 (cons_0 z_3 xs_0)))))
(assert (forall ((x_7 Nat_0))
	(elem_0 false_0 x_7 nil_0)))
(assert (forall ((x_26 list_0) (x_25 Bool_0) (x_8 Nat_0) (y_5 Nat_0) (z_4 list_0))
	(=>	(and (diseqBool_0 x_25 true_0)
			(drop_0 x_26 y_5 z_4)
			(elem_0 true_0 x_8 x_26)
			(elem_0 x_25 x_8 z_4))
		false)))
(check-sat)