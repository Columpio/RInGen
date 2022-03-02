(set-logic HORN)
(declare-datatypes ((Nat_1 0)) (((Z_2 ) (Z_3 (unS_0 Nat_1)))))
(declare-fun diseqNat_1 (Nat_1 Nat_1) Bool)
(declare-fun unS_1 (Nat_1 Nat_1) Bool)
(declare-fun isZ_3 (Nat_1) Bool)
(declare-fun isZ_4 (Nat_1) Bool)
(assert (forall ((x_34 Nat_1))
	(unS_1 x_34 (Z_3 x_34))))
(assert (isZ_3 Z_2))
(assert (forall ((x_36 Nat_1))
	(isZ_4 (Z_3 x_36))))
(assert (forall ((x_37 Nat_1))
	(diseqNat_1 Z_2 (Z_3 x_37))))
(assert (forall ((x_38 Nat_1))
	(diseqNat_1 (Z_3 x_38) Z_2)))
(assert (forall ((x_39 Nat_1) (x_40 Nat_1))
	(=> (diseqNat_1 x_39 x_40)
	    (diseqNat_1 (Z_3 x_39) (Z_3 x_40)))))
(declare-fun add_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun minus_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun le_0 (Nat_1 Nat_1) Bool)
(declare-fun ge_0 (Nat_1 Nat_1) Bool)
(declare-fun lt_0 (Nat_1 Nat_1) Bool)
(declare-fun gt_0 (Nat_1 Nat_1) Bool)
(declare-fun mult_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun div_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun mod_0 (Nat_1 Nat_1 Nat_1) Bool)
(assert (forall ((y_1 Nat_1))
	(add_0 y_1 Z_2 y_1)))
(assert (forall ((r_0 Nat_1) (x_10 Nat_1) (y_1 Nat_1))
	(=> (add_0 r_0 x_10 y_1)
	    (add_0 (Z_3 r_0) (Z_3 x_10) y_1))))
(assert (forall ((y_1 Nat_1))
	(minus_0 Z_2 Z_2 y_1)))
(assert (forall ((r_0 Nat_1) (x_10 Nat_1) (y_1 Nat_1))
	(=> (minus_0 r_0 x_10 y_1)
	    (minus_0 (Z_3 r_0) (Z_3 x_10) y_1))))
(assert (forall ((y_1 Nat_1))
	(le_0 Z_2 y_1)))
(assert (forall ((x_10 Nat_1) (y_1 Nat_1))
	(=> (le_0 x_10 y_1)
	    (le_0 (Z_3 x_10) (Z_3 y_1)))))
(assert (forall ((y_1 Nat_1))
	(ge_0 y_1 Z_2)))
(assert (forall ((x_10 Nat_1) (y_1 Nat_1))
	(=> (ge_0 x_10 y_1)
	    (ge_0 (Z_3 x_10) (Z_3 y_1)))))
(assert (forall ((y_1 Nat_1))
	(lt_0 Z_2 (Z_3 y_1))))
(assert (forall ((x_10 Nat_1) (y_1 Nat_1))
	(=> (lt_0 x_10 y_1)
	    (lt_0 (Z_3 x_10) (Z_3 y_1)))))
(assert (forall ((y_1 Nat_1))
	(gt_0 (Z_3 y_1) Z_2)))
(assert (forall ((x_10 Nat_1) (y_1 Nat_1))
	(=> (gt_0 x_10 y_1)
	    (gt_0 (Z_3 x_10) (Z_3 y_1)))))
(assert (forall ((y_1 Nat_1))
	(mult_0 Z_2 Z_2 y_1)))
(assert (forall ((r_0 Nat_1) (x_10 Nat_1) (y_1 Nat_1) (z_4 Nat_1))
	(=>	(and (mult_0 r_0 x_10 y_1)
			(add_0 z_4 r_0 y_1))
		(mult_0 z_4 (Z_3 x_10) y_1))))
(assert (forall ((x_10 Nat_1) (y_1 Nat_1))
	(=> (lt_0 x_10 y_1)
	    (div_0 Z_2 x_10 y_1))))
(assert (forall ((r_0 Nat_1) (x_10 Nat_1) (y_1 Nat_1) (z_4 Nat_1))
	(=>	(and (ge_0 x_10 y_1)
			(minus_0 z_4 x_10 y_1)
			(div_0 r_0 z_4 y_1))
		(div_0 (Z_3 r_0) x_10 y_1))))
(assert (forall ((x_10 Nat_1) (y_1 Nat_1))
	(=> (lt_0 x_10 y_1)
	    (mod_0 x_10 x_10 y_1))))
(assert (forall ((r_0 Nat_1) (x_10 Nat_1) (y_1 Nat_1) (z_4 Nat_1))
	(=>	(and (ge_0 x_10 y_1)
			(minus_0 z_4 x_10 y_1)
			(mod_0 r_0 z_4 y_1))
		(mod_0 r_0 x_10 y_1))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_1) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_1 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_12 Nat_1) (x_13 list_0))
	(head_1 x_12 (cons_0 x_12 x_13))))
(assert (forall ((x_12 Nat_1) (x_13 list_0))
	(tail_1 x_13 (cons_0 x_12 x_13))))
(assert (isnil_0 nil_0))
(assert (forall ((x_15 Nat_1) (x_16 list_0))
	(iscons_0 (cons_0 x_15 x_16))))
(assert (forall ((x_17 Nat_1) (x_18 list_0))
	(diseqlist_0 nil_0 (cons_0 x_17 x_18))))
(assert (forall ((x_19 Nat_1) (x_20 list_0))
	(diseqlist_0 (cons_0 x_19 x_20) nil_0)))
(assert (forall ((x_21 Nat_1) (x_22 list_0) (x_23 Nat_1) (x_24 list_0))
	(=> (diseqNat_1 x_21 x_23)
	    (diseqlist_0 (cons_0 x_21 x_22) (cons_0 x_23 x_24)))))
(assert (forall ((x_21 Nat_1) (x_22 list_0) (x_23 Nat_1) (x_24 list_0))
	(=> (diseqlist_0 x_22 x_24)
	    (diseqlist_0 (cons_0 x_21 x_22) (cons_0 x_23 x_24)))))
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_26 Nat_0))
	(projS_1 x_26 (S_0 x_26))))
(assert (isZ_2 Z_0))
(assert (forall ((x_28 Nat_0))
	(isS_0 (S_0 x_28))))
(assert (forall ((x_29 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_29))))
(assert (forall ((x_30 Nat_0))
	(diseqNat_0 (S_0 x_30) Z_0)))
(assert (forall ((x_31 Nat_0) (x_32 Nat_0))
	(=> (diseqNat_0 x_31 x_32)
	    (diseqNat_0 (S_0 x_31) (S_0 x_32)))))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_4 list_0) (x_1 Nat_1) (x_2 list_0) (z_1 Nat_0))
	(=> (drop_0 x_4 z_1 x_2)
	    (drop_0 x_4 (S_0 z_1) (cons_0 x_1 x_2)))))
(assert (forall ((z_1 Nat_0))
	(drop_0 nil_0 (S_0 z_1) nil_0)))
(assert (forall ((x_7 list_0))
	(drop_0 x_7 Z_0 x_7)))
(assert (forall ((x_8 list_0) (x_9 list_0) (n_0 Nat_0) (x_3 Nat_1) (xs_0 list_0))
	(=>	(and (diseqlist_0 x_8 x_9)
			(drop_0 x_8 (S_0 n_0) (cons_0 x_3 xs_0))
			(drop_0 x_9 n_0 xs_0))
		false)))
(check-sat)