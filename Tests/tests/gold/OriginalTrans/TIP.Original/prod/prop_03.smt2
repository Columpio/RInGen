(set-logic HORN)
(declare-datatypes ((Nat_1 0)) (((Z_3 ) (Z_4 (unS_0 Nat_1)))))
(declare-fun diseqNat_1 (Nat_1 Nat_1) Bool)
(declare-fun unS_1 (Nat_1 Nat_1) Bool)
(declare-fun isZ_3 (Nat_1) Bool)
(declare-fun isZ_4 (Nat_1) Bool)
(assert (forall ((x_44 Nat_1))
	(unS_1 x_44 (Z_4 x_44))))
(assert (isZ_3 Z_3))
(assert (forall ((x_46 Nat_1))
	(isZ_4 (Z_4 x_46))))
(assert (forall ((x_47 Nat_1))
	(diseqNat_1 Z_3 (Z_4 x_47))))
(assert (forall ((x_48 Nat_1))
	(diseqNat_1 (Z_4 x_48) Z_3)))
(assert (forall ((x_49 Nat_1) (x_50 Nat_1))
	(=> (diseqNat_1 x_49 x_50)
	    (diseqNat_1 (Z_4 x_49) (Z_4 x_50)))))
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
(assert (forall ((r_0 Nat_1) (x_20 Nat_1) (y_4 Nat_1))
	(=> (add_0 r_0 x_20 y_4)
	    (add_0 (Z_4 r_0) (Z_4 x_20) y_4))))
(assert (forall ((y_4 Nat_1))
	(minus_0 Z_3 Z_3 y_4)))
(assert (forall ((r_0 Nat_1) (x_20 Nat_1) (y_4 Nat_1))
	(=> (minus_0 r_0 x_20 y_4)
	    (minus_0 (Z_4 r_0) (Z_4 x_20) y_4))))
(assert (forall ((y_4 Nat_1))
	(le_0 Z_3 y_4)))
(assert (forall ((x_20 Nat_1) (y_4 Nat_1))
	(=> (le_0 x_20 y_4)
	    (le_0 (Z_4 x_20) (Z_4 y_4)))))
(assert (forall ((y_4 Nat_1))
	(ge_0 y_4 Z_3)))
(assert (forall ((x_20 Nat_1) (y_4 Nat_1))
	(=> (ge_0 x_20 y_4)
	    (ge_0 (Z_4 x_20) (Z_4 y_4)))))
(assert (forall ((y_4 Nat_1))
	(lt_0 Z_3 (Z_4 y_4))))
(assert (forall ((x_20 Nat_1) (y_4 Nat_1))
	(=> (lt_0 x_20 y_4)
	    (lt_0 (Z_4 x_20) (Z_4 y_4)))))
(assert (forall ((y_4 Nat_1))
	(gt_0 (Z_4 y_4) Z_3)))
(assert (forall ((x_20 Nat_1) (y_4 Nat_1))
	(=> (gt_0 x_20 y_4)
	    (gt_0 (Z_4 x_20) (Z_4 y_4)))))
(assert (forall ((y_4 Nat_1))
	(mult_0 Z_3 Z_3 y_4)))
(assert (forall ((r_0 Nat_1) (x_20 Nat_1) (y_4 Nat_1) (z_5 Nat_1))
	(=>	(and (mult_0 r_0 x_20 y_4)
			(add_0 z_5 r_0 y_4))
		(mult_0 z_5 (Z_4 x_20) y_4))))
(assert (forall ((x_20 Nat_1) (y_4 Nat_1))
	(=> (lt_0 x_20 y_4)
	    (div_0 Z_3 x_20 y_4))))
(assert (forall ((r_0 Nat_1) (x_20 Nat_1) (y_4 Nat_1) (z_5 Nat_1))
	(=>	(and (ge_0 x_20 y_4)
			(minus_0 z_5 x_20 y_4)
			(div_0 r_0 z_5 y_4))
		(div_0 (Z_4 r_0) x_20 y_4))))
(assert (forall ((x_20 Nat_1) (y_4 Nat_1))
	(=> (lt_0 x_20 y_4)
	    (mod_0 x_20 x_20 y_4))))
(assert (forall ((r_0 Nat_1) (x_20 Nat_1) (y_4 Nat_1) (z_5 Nat_1))
	(=>	(and (ge_0 x_20 y_4)
			(minus_0 z_5 x_20 y_4)
			(mod_0 r_0 z_5 y_4))
		(mod_0 r_0 x_20 y_4))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_1) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_1 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_22 Nat_1) (x_23 list_0))
	(head_1 x_22 (cons_0 x_22 x_23))))
(assert (forall ((x_22 Nat_1) (x_23 list_0))
	(tail_1 x_23 (cons_0 x_22 x_23))))
(assert (isnil_0 nil_0))
(assert (forall ((x_25 Nat_1) (x_26 list_0))
	(iscons_0 (cons_0 x_25 x_26))))
(assert (forall ((x_27 Nat_1) (x_28 list_0))
	(diseqlist_0 nil_0 (cons_0 x_27 x_28))))
(assert (forall ((x_29 Nat_1) (x_30 list_0))
	(diseqlist_0 (cons_0 x_29 x_30) nil_0)))
(assert (forall ((x_31 Nat_1) (x_32 list_0) (x_33 Nat_1) (x_34 list_0))
	(=> (diseqNat_1 x_31 x_33)
	    (diseqlist_0 (cons_0 x_31 x_32) (cons_0 x_33 x_34)))))
(assert (forall ((x_31 Nat_1) (x_32 list_0) (x_33 Nat_1) (x_34 list_0))
	(=> (diseqlist_0 x_32 x_34)
	    (diseqlist_0 (cons_0 x_31 x_32) (cons_0 x_33 x_34)))))
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
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_7 Nat_0) (y_0 Nat_1) (xs_0 list_0))
	(=> (length_0 x_7 xs_0)
	    (length_0 (S_0 x_7) (cons_0 y_0 xs_0)))))
(assert (length_0 Z_0 nil_0))
(declare-fun x_1 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_10 Nat_0) (z_1 Nat_0) (y_1 Nat_0))
	(=> (x_1 x_10 z_1 y_1)
	    (x_1 (S_0 x_10) (S_0 z_1) y_1))))
(assert (forall ((x_11 Nat_0))
	(x_1 x_11 Z_0 x_11)))
(declare-fun x_3 (list_0 list_0 list_0) Bool)
(assert (forall ((x_13 list_0) (z_2 Nat_1) (xs_1 list_0) (y_2 list_0))
	(=> (x_3 x_13 xs_1 y_2)
	    (x_3 (cons_0 z_2 x_13) (cons_0 z_2 xs_1) y_2))))
(assert (forall ((x_14 list_0))
	(x_3 x_14 nil_0 x_14)))
(assert (forall ((x_15 list_0) (x_16 Nat_0) (x_17 Nat_0) (x_18 Nat_0) (x_19 Nat_0) (x_5 list_0) (y_3 list_0))
	(=>	(and (diseqNat_0 x_16 x_19)
			(x_3 x_15 x_5 y_3)
			(length_0 x_16 x_15)
			(length_0 x_17 y_3)
			(length_0 x_18 x_5)
			(x_1 x_19 x_17 x_18))
		false)))
(check-sat)