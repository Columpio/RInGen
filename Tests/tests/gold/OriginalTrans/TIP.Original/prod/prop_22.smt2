(set-logic HORN)
(declare-datatypes ((Nat_1 0)) (((Z_3 ) (Z_4 (unS_0 Nat_1)))))
(declare-fun diseqNat_1 (Nat_1 Nat_1) Bool)
(declare-fun unS_1 (Nat_1 Nat_1) Bool)
(declare-fun isZ_3 (Nat_1) Bool)
(declare-fun isZ_4 (Nat_1) Bool)
(assert (forall ((x_47 Nat_1))
	(unS_1 x_47 (Z_4 x_47))))
(assert (isZ_3 Z_3))
(assert (forall ((x_49 Nat_1))
	(isZ_4 (Z_4 x_49))))
(assert (forall ((x_50 Nat_1))
	(diseqNat_1 Z_3 (Z_4 x_50))))
(assert (forall ((x_51 Nat_1))
	(diseqNat_1 (Z_4 x_51) Z_3)))
(assert (forall ((x_52 Nat_1) (x_53 Nat_1))
	(=> (diseqNat_1 x_52 x_53)
	    (diseqNat_1 (Z_4 x_52) (Z_4 x_53)))))
(declare-fun add_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun minus_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun le_0 (Nat_1 Nat_1) Bool)
(declare-fun ge_0 (Nat_1 Nat_1) Bool)
(declare-fun lt_0 (Nat_1 Nat_1) Bool)
(declare-fun gt_0 (Nat_1 Nat_1) Bool)
(declare-fun mult_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun div_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun mod_0 (Nat_1 Nat_1 Nat_1) Bool)
(assert (forall ((y_4 Nat_1))
	(add_0 y_4 Z_3 y_4)))
(assert (forall ((r_0 Nat_1) (x_21 Nat_1) (y_4 Nat_1))
	(=> (add_0 r_0 x_21 y_4)
	    (add_0 (Z_4 r_0) (Z_4 x_21) y_4))))
(assert (forall ((y_4 Nat_1))
	(minus_0 Z_3 Z_3 y_4)))
(assert (forall ((r_0 Nat_1) (x_21 Nat_1) (y_4 Nat_1))
	(=> (minus_0 r_0 x_21 y_4)
	    (minus_0 (Z_4 r_0) (Z_4 x_21) y_4))))
(assert (forall ((y_4 Nat_1))
	(le_0 Z_3 y_4)))
(assert (forall ((x_21 Nat_1) (y_4 Nat_1))
	(=> (le_0 x_21 y_4)
	    (le_0 (Z_4 x_21) (Z_4 y_4)))))
(assert (forall ((y_4 Nat_1))
	(ge_0 y_4 Z_3)))
(assert (forall ((x_21 Nat_1) (y_4 Nat_1))
	(=> (ge_0 x_21 y_4)
	    (ge_0 (Z_4 x_21) (Z_4 y_4)))))
(assert (forall ((y_4 Nat_1))
	(lt_0 Z_3 (Z_4 y_4))))
(assert (forall ((x_21 Nat_1) (y_4 Nat_1))
	(=> (lt_0 x_21 y_4)
	    (lt_0 (Z_4 x_21) (Z_4 y_4)))))
(assert (forall ((y_4 Nat_1))
	(gt_0 (Z_4 y_4) Z_3)))
(assert (forall ((x_21 Nat_1) (y_4 Nat_1))
	(=> (gt_0 x_21 y_4)
	    (gt_0 (Z_4 x_21) (Z_4 y_4)))))
(assert (forall ((y_4 Nat_1))
	(mult_0 Z_3 Z_3 y_4)))
(assert (forall ((r_0 Nat_1) (x_21 Nat_1) (y_4 Nat_1) (z_5 Nat_1))
	(=>	(and (mult_0 r_0 x_21 y_4)
			(add_0 z_5 r_0 y_4))
		(mult_0 z_5 (Z_4 x_21) y_4))))
(assert (forall ((x_21 Nat_1) (y_4 Nat_1))
	(=> (lt_0 x_21 y_4)
	    (div_0 Z_3 x_21 y_4))))
(assert (forall ((r_0 Nat_1) (x_21 Nat_1) (y_4 Nat_1) (z_5 Nat_1))
	(=>	(and (ge_0 x_21 y_4)
			(minus_0 z_5 x_21 y_4)
			(div_0 r_0 z_5 y_4))
		(div_0 (Z_4 r_0) x_21 y_4))))
(assert (forall ((x_21 Nat_1) (y_4 Nat_1))
	(=> (lt_0 x_21 y_4)
	    (mod_0 x_21 x_21 y_4))))
(assert (forall ((r_0 Nat_1) (x_21 Nat_1) (y_4 Nat_1) (z_5 Nat_1))
	(=>	(and (ge_0 x_21 y_4)
			(minus_0 z_5 x_21 y_4)
			(mod_0 r_0 z_5 y_4))
		(mod_0 r_0 x_21 y_4))))
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
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_1) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_1 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_25 Nat_1) (x_26 list_0))
	(head_1 x_25 (cons_0 x_25 x_26))))
(assert (forall ((x_25 Nat_1) (x_26 list_0))
	(tail_1 x_26 (cons_0 x_25 x_26))))
(assert (isnil_0 nil_0))
(assert (forall ((x_28 Nat_1) (x_29 list_0))
	(iscons_0 (cons_0 x_28 x_29))))
(assert (forall ((x_30 Nat_1) (x_31 list_0))
	(diseqlist_0 nil_0 (cons_0 x_30 x_31))))
(assert (forall ((x_32 Nat_1) (x_33 list_0))
	(diseqlist_0 (cons_0 x_32 x_33) nil_0)))
(assert (forall ((x_34 Nat_1) (x_35 list_0) (x_36 Nat_1) (x_37 list_0))
	(=> (diseqNat_1 x_34 x_36)
	    (diseqlist_0 (cons_0 x_34 x_35) (cons_0 x_36 x_37)))))
(assert (forall ((x_34 Nat_1) (x_35 list_0) (x_36 Nat_1) (x_37 list_0))
	(=> (diseqlist_0 x_35 x_37)
	    (diseqlist_0 (cons_0 x_34 x_35) (cons_0 x_36 x_37)))))
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_39 Nat_0))
	(projS_1 x_39 (S_0 x_39))))
(assert (isZ_2 Z_0))
(assert (forall ((x_41 Nat_0))
	(isS_0 (S_0 x_41))))
(assert (forall ((x_42 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_42))))
(assert (forall ((x_43 Nat_0))
	(diseqNat_0 (S_0 x_43) Z_0)))
(assert (forall ((x_44 Nat_0) (x_45 Nat_0))
	(=> (diseqNat_0 x_44 x_45)
	    (diseqNat_0 (S_0 x_44) (S_0 x_45)))))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_6 Nat_0) (y_0 Nat_1) (xs_0 list_0))
	(=> (length_0 x_6 xs_0)
	    (length_0 (S_0 x_6) (cons_0 y_0 xs_0)))))
(assert (length_0 Z_0 nil_0))
(declare-fun even_0 (Bool_0 Nat_0) Bool)
(assert (forall ((x_8 Bool_0) (z_1 Nat_0))
	(=> (even_0 x_8 z_1)
	    (even_0 x_8 (S_0 (S_0 z_1))))))
(assert (even_0 false_0 (S_0 Z_0)))
(assert (even_0 true_0 Z_0))
(declare-fun x_2 (list_0 list_0 list_0) Bool)
(assert (forall ((x_13 list_0) (z_2 Nat_1) (xs_1 list_0) (y_2 list_0))
	(=> (x_2 x_13 xs_1 y_2)
	    (x_2 (cons_0 z_2 x_13) (cons_0 z_2 xs_1) y_2))))
(assert (forall ((x_14 list_0))
	(x_2 x_14 nil_0 x_14)))
(assert (forall ((x_15 list_0) (x_16 Nat_0) (x_17 Bool_0) (x_18 list_0) (x_19 Nat_0) (x_20 Bool_0) (x_4 list_0) (y_3 list_0))
	(=>	(and (diseqBool_0 x_17 x_20)
			(x_2 x_15 x_4 y_3)
			(length_0 x_16 x_15)
			(even_0 x_17 x_16)
			(x_2 x_18 y_3 x_4)
			(length_0 x_19 x_18)
			(even_0 x_20 x_19))
		false)))
(check-sat)
