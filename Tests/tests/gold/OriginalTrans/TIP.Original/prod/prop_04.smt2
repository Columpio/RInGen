(set-logic HORN)
(declare-datatypes ((Nat_1 0)) (((Z_2 ) (Z_3 (unS_0 Nat_1)))))
(declare-fun diseqNat_1 (Nat_1 Nat_1) Bool)
(declare-fun unS_1 (Nat_1 Nat_1) Bool)
(declare-fun isZ_3 (Nat_1) Bool)
(declare-fun isZ_4 (Nat_1) Bool)
(assert (forall ((x_42 Nat_1))
	(unS_1 x_42 (Z_3 x_42))))
(assert (isZ_3 Z_2))
(assert (forall ((x_44 Nat_1))
	(isZ_4 (Z_3 x_44))))
(assert (forall ((x_45 Nat_1))
	(diseqNat_1 Z_2 (Z_3 x_45))))
(assert (forall ((x_46 Nat_1))
	(diseqNat_1 (Z_3 x_46) Z_2)))
(assert (forall ((x_47 Nat_1) (x_48 Nat_1))
	(=> (diseqNat_1 x_47 x_48)
	    (diseqNat_1 (Z_3 x_47) (Z_3 x_48)))))
(declare-fun add_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun minus_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun le_0 (Nat_1 Nat_1) Bool)
(declare-fun ge_0 (Nat_1 Nat_1) Bool)
(declare-fun lt_0 (Nat_1 Nat_1) Bool)
(declare-fun gt_0 (Nat_1 Nat_1) Bool)
(declare-fun mult_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun div_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun mod_0 (Nat_1 Nat_1 Nat_1) Bool)
(assert (forall ((y_3 Nat_1))
	(add_0 y_3 Z_2 y_3)))
(assert (forall ((r_0 Nat_1) (x_18 Nat_1) (y_3 Nat_1))
	(=> (add_0 r_0 x_18 y_3)
	    (add_0 (Z_3 r_0) (Z_3 x_18) y_3))))
(assert (forall ((y_3 Nat_1))
	(minus_0 Z_2 Z_2 y_3)))
(assert (forall ((r_0 Nat_1) (x_18 Nat_1) (y_3 Nat_1))
	(=> (minus_0 r_0 x_18 y_3)
	    (minus_0 (Z_3 r_0) (Z_3 x_18) y_3))))
(assert (forall ((y_3 Nat_1))
	(le_0 Z_2 y_3)))
(assert (forall ((x_18 Nat_1) (y_3 Nat_1))
	(=> (le_0 x_18 y_3)
	    (le_0 (Z_3 x_18) (Z_3 y_3)))))
(assert (forall ((y_3 Nat_1))
	(ge_0 y_3 Z_2)))
(assert (forall ((x_18 Nat_1) (y_3 Nat_1))
	(=> (ge_0 x_18 y_3)
	    (ge_0 (Z_3 x_18) (Z_3 y_3)))))
(assert (forall ((y_3 Nat_1))
	(lt_0 Z_2 (Z_3 y_3))))
(assert (forall ((x_18 Nat_1) (y_3 Nat_1))
	(=> (lt_0 x_18 y_3)
	    (lt_0 (Z_3 x_18) (Z_3 y_3)))))
(assert (forall ((y_3 Nat_1))
	(gt_0 (Z_3 y_3) Z_2)))
(assert (forall ((x_18 Nat_1) (y_3 Nat_1))
	(=> (gt_0 x_18 y_3)
	    (gt_0 (Z_3 x_18) (Z_3 y_3)))))
(assert (forall ((y_3 Nat_1))
	(mult_0 Z_2 Z_2 y_3)))
(assert (forall ((r_0 Nat_1) (x_18 Nat_1) (y_3 Nat_1) (z_4 Nat_1))
	(=>	(and (mult_0 r_0 x_18 y_3)
			(add_0 z_4 r_0 y_3))
		(mult_0 z_4 (Z_3 x_18) y_3))))
(assert (forall ((x_18 Nat_1) (y_3 Nat_1))
	(=> (lt_0 x_18 y_3)
	    (div_0 Z_2 x_18 y_3))))
(assert (forall ((r_0 Nat_1) (x_18 Nat_1) (y_3 Nat_1) (z_4 Nat_1))
	(=>	(and (ge_0 x_18 y_3)
			(minus_0 z_4 x_18 y_3)
			(div_0 r_0 z_4 y_3))
		(div_0 (Z_3 r_0) x_18 y_3))))
(assert (forall ((x_18 Nat_1) (y_3 Nat_1))
	(=> (lt_0 x_18 y_3)
	    (mod_0 x_18 x_18 y_3))))
(assert (forall ((r_0 Nat_1) (x_18 Nat_1) (y_3 Nat_1) (z_4 Nat_1))
	(=>	(and (ge_0 x_18 y_3)
			(minus_0 z_4 x_18 y_3)
			(mod_0 r_0 z_4 y_3))
		(mod_0 r_0 x_18 y_3))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_1) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_1 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_20 Nat_1) (x_21 list_0))
	(head_1 x_20 (cons_0 x_20 x_21))))
(assert (forall ((x_20 Nat_1) (x_21 list_0))
	(tail_1 x_21 (cons_0 x_20 x_21))))
(assert (isnil_0 nil_0))
(assert (forall ((x_23 Nat_1) (x_24 list_0))
	(iscons_0 (cons_0 x_23 x_24))))
(assert (forall ((x_25 Nat_1) (x_26 list_0))
	(diseqlist_0 nil_0 (cons_0 x_25 x_26))))
(assert (forall ((x_27 Nat_1) (x_28 list_0))
	(diseqlist_0 (cons_0 x_27 x_28) nil_0)))
(assert (forall ((x_29 Nat_1) (x_30 list_0) (x_31 Nat_1) (x_32 list_0))
	(=> (diseqNat_1 x_29 x_31)
	    (diseqlist_0 (cons_0 x_29 x_30) (cons_0 x_31 x_32)))))
(assert (forall ((x_29 Nat_1) (x_30 list_0) (x_31 Nat_1) (x_32 list_0))
	(=> (diseqlist_0 x_30 x_32)
	    (diseqlist_0 (cons_0 x_29 x_30) (cons_0 x_31 x_32)))))
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_34 Nat_0))
	(projS_1 x_34 (S_0 x_34))))
(assert (isZ_2 Z_0))
(assert (forall ((x_36 Nat_0))
	(isS_0 (S_0 x_36))))
(assert (forall ((x_37 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_37))))
(assert (forall ((x_38 Nat_0))
	(diseqNat_0 (S_0 x_38) Z_0)))
(assert (forall ((x_39 Nat_0) (x_40 Nat_0))
	(=> (diseqNat_0 x_39 x_40)
	    (diseqNat_0 (S_0 x_39) (S_0 x_40)))))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_6 Nat_0) (y_0 Nat_1) (xs_0 list_0))
	(=> (length_0 x_6 xs_0)
	    (length_0 (S_0 x_6) (cons_0 y_0 xs_0)))))
(assert (length_0 Z_0 nil_0))
(declare-fun double_0 (Nat_0 Nat_0) Bool)
(assert (forall ((x_9 Nat_0) (y_1 Nat_0))
	(=> (double_0 x_9 y_1)
	    (double_0 (S_0 (S_0 x_9)) (S_0 y_1)))))
(assert (double_0 Z_0 Z_0))
(declare-fun x_2 (list_0 list_0 list_0) Bool)
(assert (forall ((x_12 list_0) (z_1 Nat_1) (xs_1 list_0) (y_2 list_0))
	(=> (x_2 x_12 xs_1 y_2)
	    (x_2 (cons_0 z_1 x_12) (cons_0 z_1 xs_1) y_2))))
(assert (forall ((x_13 list_0))
	(x_2 x_13 nil_0 x_13)))
(assert (forall ((x_14 list_0) (x_15 Nat_0) (x_16 Nat_0) (x_17 Nat_0) (x_4 list_0))
	(=>	(and (diseqNat_0 x_15 x_17)
			(x_2 x_14 x_4 x_4)
			(length_0 x_15 x_14)
			(length_0 x_16 x_4)
			(double_0 x_17 x_16))
		false)))
(check-sat)
