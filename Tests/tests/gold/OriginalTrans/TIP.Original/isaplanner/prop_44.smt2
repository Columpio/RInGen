(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_2 ) (Z_3 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_54 Nat_0))
	(unS_1 x_54 (Z_3 x_54))))
(assert (isZ_2 Z_2))
(assert (forall ((x_56 Nat_0))
	(isZ_3 (Z_3 x_56))))
(assert (forall ((x_57 Nat_0))
	(diseqNat_0 Z_2 (Z_3 x_57))))
(assert (forall ((x_58 Nat_0))
	(diseqNat_0 (Z_3 x_58) Z_2)))
(assert (forall ((x_59 Nat_0) (x_60 Nat_0))
	(=> (diseqNat_0 x_59 x_60)
	    (diseqNat_0 (Z_3 x_59) (Z_3 x_60)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_3 Nat_0))
	(add_0 y_3 Z_2 y_3)))
(assert (forall ((r_0 Nat_0) (x_15 Nat_0) (y_3 Nat_0))
	(=> (add_0 r_0 x_15 y_3)
	    (add_0 (Z_3 r_0) (Z_3 x_15) y_3))))
(assert (forall ((y_3 Nat_0))
	(minus_0 Z_2 Z_2 y_3)))
(assert (forall ((r_0 Nat_0) (x_15 Nat_0) (y_3 Nat_0))
	(=> (minus_0 r_0 x_15 y_3)
	    (minus_0 (Z_3 r_0) (Z_3 x_15) y_3))))
(assert (forall ((y_3 Nat_0))
	(le_0 Z_2 y_3)))
(assert (forall ((x_15 Nat_0) (y_3 Nat_0))
	(=> (le_0 x_15 y_3)
	    (le_0 (Z_3 x_15) (Z_3 y_3)))))
(assert (forall ((y_3 Nat_0))
	(ge_0 y_3 Z_2)))
(assert (forall ((x_15 Nat_0) (y_3 Nat_0))
	(=> (ge_0 x_15 y_3)
	    (ge_0 (Z_3 x_15) (Z_3 y_3)))))
(assert (forall ((y_3 Nat_0))
	(lt_0 Z_2 (Z_3 y_3))))
(assert (forall ((x_15 Nat_0) (y_3 Nat_0))
	(=> (lt_0 x_15 y_3)
	    (lt_0 (Z_3 x_15) (Z_3 y_3)))))
(assert (forall ((y_3 Nat_0))
	(gt_0 (Z_3 y_3) Z_2)))
(assert (forall ((x_15 Nat_0) (y_3 Nat_0))
	(=> (gt_0 x_15 y_3)
	    (gt_0 (Z_3 x_15) (Z_3 y_3)))))
(assert (forall ((y_3 Nat_0))
	(mult_0 Z_2 Z_2 y_3)))
(assert (forall ((r_0 Nat_0) (x_15 Nat_0) (y_3 Nat_0) (z_4 Nat_0))
	(=>	(and (mult_0 r_0 x_15 y_3)
			(add_0 z_4 r_0 y_3))
		(mult_0 z_4 (Z_3 x_15) y_3))))
(assert (forall ((x_15 Nat_0) (y_3 Nat_0))
	(=> (lt_0 x_15 y_3)
	    (div_0 Z_2 x_15 y_3))))
(assert (forall ((r_0 Nat_0) (x_15 Nat_0) (y_3 Nat_0) (z_4 Nat_0))
	(=>	(and (ge_0 x_15 y_3)
			(minus_0 z_4 x_15 y_3)
			(div_0 r_0 z_4 y_3))
		(div_0 (Z_3 r_0) x_15 y_3))))
(assert (forall ((x_15 Nat_0) (y_3 Nat_0))
	(=> (lt_0 x_15 y_3)
	    (mod_0 x_15 x_15 y_3))))
(assert (forall ((r_0 Nat_0) (x_15 Nat_0) (y_3 Nat_0) (z_4 Nat_0))
	(=>	(and (ge_0 x_15 y_3)
			(minus_0 z_4 x_15 y_3)
			(mod_0 r_0 z_4 y_3))
		(mod_0 r_0 x_15 y_3))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 Nat_0) (projpair_1 Nat_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (Nat_0 pair_0) Bool)
(declare-fun projpair_3 (Nat_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_16 Nat_0) (x_17 Nat_0))
	(projpair_2 x_16 (pair_1 x_16 x_17))))
(assert (forall ((x_16 Nat_0) (x_17 Nat_0))
	(projpair_3 x_17 (pair_1 x_16 x_17))))
(assert (forall ((x_19 Nat_0) (x_20 Nat_0))
	(ispair_0 (pair_1 x_19 x_20))))
(assert (forall ((x_21 Nat_0) (x_22 Nat_0) (x_23 Nat_0) (x_24 Nat_0))
	(=> (diseqNat_0 x_21 x_23)
	    (diseqpair_0 (pair_1 x_21 x_22) (pair_1 x_23 x_24)))))
(assert (forall ((x_21 Nat_0) (x_22 Nat_0) (x_23 Nat_0) (x_24 Nat_0))
	(=> (diseqNat_0 x_22 x_24)
	    (diseqpair_0 (pair_1 x_21 x_22) (pair_1 x_23 x_24)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_2 (Nat_0 list_0) Bool)
(declare-fun tail_2 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_26 Nat_0) (x_27 list_0))
	(head_2 x_26 (cons_0 x_26 x_27))))
(assert (forall ((x_26 Nat_0) (x_27 list_0))
	(tail_2 x_27 (cons_0 x_26 x_27))))
(assert (isnil_0 nil_0))
(assert (forall ((x_29 Nat_0) (x_30 list_0))
	(iscons_0 (cons_0 x_29 x_30))))
(assert (forall ((x_31 Nat_0) (x_32 list_0))
	(diseqlist_0 nil_0 (cons_0 x_31 x_32))))
(assert (forall ((x_33 Nat_0) (x_34 list_0))
	(diseqlist_0 (cons_0 x_33 x_34) nil_0)))
(assert (forall ((x_35 Nat_0) (x_36 list_0) (x_37 Nat_0) (x_38 list_0))
	(=> (diseqNat_0 x_35 x_37)
	    (diseqlist_0 (cons_0 x_35 x_36) (cons_0 x_37 x_38)))))
(assert (forall ((x_35 Nat_0) (x_36 list_0) (x_37 Nat_0) (x_38 list_0))
	(=> (diseqlist_0 x_36 x_38)
	    (diseqlist_0 (cons_0 x_35 x_36) (cons_0 x_37 x_38)))))
(declare-datatypes ((list_1 0)) (((nil_1 ) (cons_1 (head_1 pair_0) (tail_1 list_1)))))
(declare-fun diseqlist_1 (list_1 list_1) Bool)
(declare-fun head_3 (pair_0 list_1) Bool)
(declare-fun tail_3 (list_1 list_1) Bool)
(declare-fun isnil_1 (list_1) Bool)
(declare-fun iscons_1 (list_1) Bool)
(assert (forall ((x_40 pair_0) (x_41 list_1))
	(head_3 x_40 (cons_1 x_40 x_41))))
(assert (forall ((x_40 pair_0) (x_41 list_1))
	(tail_3 x_41 (cons_1 x_40 x_41))))
(assert (isnil_1 nil_1))
(assert (forall ((x_43 pair_0) (x_44 list_1))
	(iscons_1 (cons_1 x_43 x_44))))
(assert (forall ((x_45 pair_0) (x_46 list_1))
	(diseqlist_1 nil_1 (cons_1 x_45 x_46))))
(assert (forall ((x_47 pair_0) (x_48 list_1))
	(diseqlist_1 (cons_1 x_47 x_48) nil_1)))
(assert (forall ((x_49 pair_0) (x_50 list_1) (x_51 pair_0) (x_52 list_1))
	(=> (diseqpair_0 x_49 x_51)
	    (diseqlist_1 (cons_1 x_49 x_50) (cons_1 x_51 x_52)))))
(assert (forall ((x_49 pair_0) (x_50 list_1) (x_51 pair_0) (x_52 list_1))
	(=> (diseqlist_1 x_50 x_52)
	    (diseqlist_1 (cons_1 x_49 x_50) (cons_1 x_51 x_52)))))
(declare-fun zip_0 (list_1 list_0 list_0) Bool)
(assert (forall ((x_7 list_1) (x_2 Nat_0) (x_3 list_0) (z_0 Nat_0) (x_1 list_0))
	(=> (zip_0 x_7 x_1 x_3)
	    (zip_0 (cons_1 (pair_1 z_0 x_2) x_7) (cons_0 z_0 x_1) (cons_0 x_2 x_3)))))
(assert (forall ((z_0 Nat_0) (x_1 list_0))
	(zip_0 nil_1 (cons_0 z_0 x_1) nil_0)))
(assert (forall ((y_0 list_0))
	(zip_0 nil_1 nil_0 y_0)))
(declare-fun zipConcat_0 (list_1 Nat_0 list_0 list_0) Bool)
(assert (forall ((x_11 list_1) (y_2 Nat_0) (ys_0 list_0) (x_4 Nat_0) (y_1 list_0))
	(=> (zip_0 x_11 y_1 ys_0)
	    (zipConcat_0 (cons_1 (pair_1 x_4 y_2) x_11) x_4 y_1 (cons_0 y_2 ys_0)))))
(assert (forall ((x_4 Nat_0) (y_1 list_0))
	(zipConcat_0 nil_1 x_4 y_1 nil_0)))
(assert (forall ((x_13 list_1) (x_14 list_1) (x_5 Nat_0) (xs_0 list_0) (ys_1 list_0))
	(=>	(and (diseqlist_1 x_13 x_14)
			(zip_0 x_13 (cons_0 x_5 xs_0) ys_1)
			(zipConcat_0 x_14 x_5 xs_0 ys_1))
		false)))
(check-sat)
