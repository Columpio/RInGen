(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_1 ) (Z_2 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_50 Nat_0))
	(unS_1 x_50 (Z_2 x_50))))
(assert (isZ_2 Z_1))
(assert (forall ((x_52 Nat_0))
	(isZ_3 (Z_2 x_52))))
(assert (forall ((x_53 Nat_0))
	(diseqNat_0 Z_1 (Z_2 x_53))))
(assert (forall ((x_54 Nat_0))
	(diseqNat_0 (Z_2 x_54) Z_1)))
(assert (forall ((x_55 Nat_0) (x_56 Nat_0))
	(=> (diseqNat_0 x_55 x_56)
	    (diseqNat_0 (Z_2 x_55) (Z_2 x_56)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_2 Nat_0))
	(add_0 y_2 Z_1 y_2)))
(assert (forall ((r_0 Nat_0) (x_11 Nat_0) (y_2 Nat_0))
	(=> (add_0 r_0 x_11 y_2)
	    (add_0 (Z_2 r_0) (Z_2 x_11) y_2))))
(assert (forall ((y_2 Nat_0))
	(minus_0 Z_1 Z_1 y_2)))
(assert (forall ((r_0 Nat_0) (x_11 Nat_0) (y_2 Nat_0))
	(=> (minus_0 r_0 x_11 y_2)
	    (minus_0 (Z_2 r_0) (Z_2 x_11) y_2))))
(assert (forall ((y_2 Nat_0))
	(le_0 Z_1 y_2)))
(assert (forall ((x_11 Nat_0) (y_2 Nat_0))
	(=> (le_0 x_11 y_2)
	    (le_0 (Z_2 x_11) (Z_2 y_2)))))
(assert (forall ((y_2 Nat_0))
	(ge_0 y_2 Z_1)))
(assert (forall ((x_11 Nat_0) (y_2 Nat_0))
	(=> (ge_0 x_11 y_2)
	    (ge_0 (Z_2 x_11) (Z_2 y_2)))))
(assert (forall ((y_2 Nat_0))
	(lt_0 Z_1 (Z_2 y_2))))
(assert (forall ((x_11 Nat_0) (y_2 Nat_0))
	(=> (lt_0 x_11 y_2)
	    (lt_0 (Z_2 x_11) (Z_2 y_2)))))
(assert (forall ((y_2 Nat_0))
	(gt_0 (Z_2 y_2) Z_1)))
(assert (forall ((x_11 Nat_0) (y_2 Nat_0))
	(=> (gt_0 x_11 y_2)
	    (gt_0 (Z_2 x_11) (Z_2 y_2)))))
(assert (forall ((y_2 Nat_0))
	(mult_0 Z_1 Z_1 y_2)))
(assert (forall ((r_0 Nat_0) (x_11 Nat_0) (y_2 Nat_0) (z_3 Nat_0))
	(=>	(and (mult_0 r_0 x_11 y_2)
			(add_0 z_3 r_0 y_2))
		(mult_0 z_3 (Z_2 x_11) y_2))))
(assert (forall ((x_11 Nat_0) (y_2 Nat_0))
	(=> (lt_0 x_11 y_2)
	    (div_0 Z_1 x_11 y_2))))
(assert (forall ((r_0 Nat_0) (x_11 Nat_0) (y_2 Nat_0) (z_3 Nat_0))
	(=>	(and (ge_0 x_11 y_2)
			(minus_0 z_3 x_11 y_2)
			(div_0 r_0 z_3 y_2))
		(div_0 (Z_2 r_0) x_11 y_2))))
(assert (forall ((x_11 Nat_0) (y_2 Nat_0))
	(=> (lt_0 x_11 y_2)
	    (mod_0 x_11 x_11 y_2))))
(assert (forall ((r_0 Nat_0) (x_11 Nat_0) (y_2 Nat_0) (z_3 Nat_0))
	(=>	(and (ge_0 x_11 y_2)
			(minus_0 z_3 x_11 y_2)
			(mod_0 r_0 z_3 y_2))
		(mod_0 r_0 x_11 y_2))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 Nat_0) (projpair_1 Nat_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (Nat_0 pair_0) Bool)
(declare-fun projpair_3 (Nat_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_12 Nat_0) (x_13 Nat_0))
	(projpair_2 x_12 (pair_1 x_12 x_13))))
(assert (forall ((x_12 Nat_0) (x_13 Nat_0))
	(projpair_3 x_13 (pair_1 x_12 x_13))))
(assert (forall ((x_15 Nat_0) (x_16 Nat_0))
	(ispair_0 (pair_1 x_15 x_16))))
(assert (forall ((x_17 Nat_0) (x_18 Nat_0) (x_19 Nat_0) (x_20 Nat_0))
	(=> (diseqNat_0 x_17 x_19)
	    (diseqpair_0 (pair_1 x_17 x_18) (pair_1 x_19 x_20)))))
(assert (forall ((x_17 Nat_0) (x_18 Nat_0) (x_19 Nat_0) (x_20 Nat_0))
	(=> (diseqNat_0 x_18 x_20)
	    (diseqpair_0 (pair_1 x_17 x_18) (pair_1 x_19 x_20)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_2 (Nat_0 list_0) Bool)
(declare-fun tail_2 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_22 Nat_0) (x_23 list_0))
	(head_2 x_22 (cons_0 x_22 x_23))))
(assert (forall ((x_22 Nat_0) (x_23 list_0))
	(tail_2 x_23 (cons_0 x_22 x_23))))
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
(declare-datatypes ((list_1 0)) (((nil_1 ) (cons_1 (head_1 pair_0) (tail_1 list_1)))))
(declare-fun diseqlist_1 (list_1 list_1) Bool)
(declare-fun head_3 (pair_0 list_1) Bool)
(declare-fun tail_3 (list_1 list_1) Bool)
(declare-fun isnil_1 (list_1) Bool)
(declare-fun iscons_1 (list_1) Bool)
(assert (forall ((x_36 pair_0) (x_37 list_1))
	(head_3 x_36 (cons_1 x_36 x_37))))
(assert (forall ((x_36 pair_0) (x_37 list_1))
	(tail_3 x_37 (cons_1 x_36 x_37))))
(assert (isnil_1 nil_1))
(assert (forall ((x_39 pair_0) (x_40 list_1))
	(iscons_1 (cons_1 x_39 x_40))))
(assert (forall ((x_41 pair_0) (x_42 list_1))
	(diseqlist_1 nil_1 (cons_1 x_41 x_42))))
(assert (forall ((x_43 pair_0) (x_44 list_1))
	(diseqlist_1 (cons_1 x_43 x_44) nil_1)))
(assert (forall ((x_45 pair_0) (x_46 list_1) (x_47 pair_0) (x_48 list_1))
	(=> (diseqpair_0 x_45 x_47)
	    (diseqlist_1 (cons_1 x_45 x_46) (cons_1 x_47 x_48)))))
(assert (forall ((x_45 pair_0) (x_46 list_1) (x_47 pair_0) (x_48 list_1))
	(=> (diseqlist_1 x_46 x_48)
	    (diseqlist_1 (cons_1 x_45 x_46) (cons_1 x_47 x_48)))))
(declare-fun zip_0 (list_1 list_0 list_0) Bool)
(assert (forall ((x_6 list_1) (x_2 Nat_0) (x_3 list_0) (z_0 Nat_0) (x_1 list_0))
	(=> (zip_0 x_6 x_1 x_3)
	    (zip_0 (cons_1 (pair_1 z_0 x_2) x_6) (cons_0 z_0 x_1) (cons_0 x_2 x_3)))))
(assert (forall ((z_0 Nat_0) (x_1 list_0))
	(zip_0 nil_1 (cons_0 z_0 x_1) nil_0)))
(assert (forall ((y_0 list_0))
	(zip_0 nil_1 nil_0 y_0)))
(assert (forall ((x_9 list_1) (x_10 list_1) (x_4 Nat_0) (y_1 Nat_0) (xs_0 list_0) (ys_0 list_0))
	(=>	(and (diseqlist_1 x_9 (cons_1 (pair_1 x_4 y_1) x_10))
			(zip_0 x_9 (cons_0 x_4 xs_0) (cons_0 y_1 ys_0))
			(zip_0 x_10 xs_0 ys_0))
		false)))
(check-sat)
