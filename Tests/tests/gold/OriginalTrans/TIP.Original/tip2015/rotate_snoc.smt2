(set-logic HORN)
(declare-datatypes ((Nat_1 0)) (((Z_5 ) (Z_6 (unS_0 Nat_1)))))
(declare-fun diseqNat_1 (Nat_1 Nat_1) Bool)
(declare-fun unS_1 (Nat_1 Nat_1) Bool)
(declare-fun isZ_2 (Nat_1) Bool)
(declare-fun isZ_3 (Nat_1) Bool)
(assert (forall ((x_57 Nat_1))
	(unS_1 x_57 (Z_6 x_57))))
(assert (isZ_2 Z_5))
(assert (forall ((x_59 Nat_1))
	(isZ_3 (Z_6 x_59))))
(assert (forall ((x_60 Nat_1))
	(diseqNat_1 Z_5 (Z_6 x_60))))
(assert (forall ((x_61 Nat_1))
	(diseqNat_1 (Z_6 x_61) Z_5)))
(assert (forall ((x_62 Nat_1) (x_63 Nat_1))
	(=> (diseqNat_1 x_62 x_63)
	    (diseqNat_1 (Z_6 x_62) (Z_6 x_63)))))
(declare-fun add_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun minus_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun le_0 (Nat_1 Nat_1) Bool)
(declare-fun ge_0 (Nat_1 Nat_1) Bool)
(declare-fun lt_0 (Nat_1 Nat_1) Bool)
(declare-fun gt_0 (Nat_1 Nat_1) Bool)
(declare-fun mult_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun div_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun mod_0 (Nat_1 Nat_1 Nat_1) Bool)
(assert (forall ((y_6 Nat_1))
	(add_0 y_6 Z_5 y_6)))
(assert (forall ((r_0 Nat_1) (x_33 Nat_1) (y_6 Nat_1))
	(=> (add_0 r_0 x_33 y_6)
	    (add_0 (Z_6 r_0) (Z_6 x_33) y_6))))
(assert (forall ((y_6 Nat_1))
	(minus_0 Z_5 Z_5 y_6)))
(assert (forall ((r_0 Nat_1) (x_33 Nat_1) (y_6 Nat_1))
	(=> (minus_0 r_0 x_33 y_6)
	    (minus_0 (Z_6 r_0) (Z_6 x_33) y_6))))
(assert (forall ((y_6 Nat_1))
	(le_0 Z_5 y_6)))
(assert (forall ((x_33 Nat_1) (y_6 Nat_1))
	(=> (le_0 x_33 y_6)
	    (le_0 (Z_6 x_33) (Z_6 y_6)))))
(assert (forall ((y_6 Nat_1))
	(ge_0 y_6 Z_5)))
(assert (forall ((x_33 Nat_1) (y_6 Nat_1))
	(=> (ge_0 x_33 y_6)
	    (ge_0 (Z_6 x_33) (Z_6 y_6)))))
(assert (forall ((y_6 Nat_1))
	(lt_0 Z_5 (Z_6 y_6))))
(assert (forall ((x_33 Nat_1) (y_6 Nat_1))
	(=> (lt_0 x_33 y_6)
	    (lt_0 (Z_6 x_33) (Z_6 y_6)))))
(assert (forall ((y_6 Nat_1))
	(gt_0 (Z_6 y_6) Z_5)))
(assert (forall ((x_33 Nat_1) (y_6 Nat_1))
	(=> (gt_0 x_33 y_6)
	    (gt_0 (Z_6 x_33) (Z_6 y_6)))))
(assert (forall ((y_6 Nat_1))
	(mult_0 Z_5 Z_5 y_6)))
(assert (forall ((r_0 Nat_1) (x_33 Nat_1) (y_6 Nat_1) (z_7 Nat_1))
	(=>	(and (mult_0 r_0 x_33 y_6)
			(add_0 z_7 r_0 y_6))
		(mult_0 z_7 (Z_6 x_33) y_6))))
(assert (forall ((x_33 Nat_1) (y_6 Nat_1))
	(=> (lt_0 x_33 y_6)
	    (div_0 Z_5 x_33 y_6))))
(assert (forall ((r_0 Nat_1) (x_33 Nat_1) (y_6 Nat_1) (z_7 Nat_1))
	(=>	(and (ge_0 x_33 y_6)
			(minus_0 z_7 x_33 y_6)
			(div_0 r_0 z_7 y_6))
		(div_0 (Z_6 r_0) x_33 y_6))))
(assert (forall ((x_33 Nat_1) (y_6 Nat_1))
	(=> (lt_0 x_33 y_6)
	    (mod_0 x_33 x_33 y_6))))
(assert (forall ((r_0 Nat_1) (x_33 Nat_1) (y_6 Nat_1) (z_7 Nat_1))
	(=>	(and (ge_0 x_33 y_6)
			(minus_0 z_7 x_33 y_6)
			(mod_0 r_0 z_7 y_6))
		(mod_0 r_0 x_33 y_6))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_1) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_1 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_35 Nat_1) (x_36 list_0))
	(head_1 x_35 (cons_0 x_35 x_36))))
(assert (forall ((x_35 Nat_1) (x_36 list_0))
	(tail_1 x_36 (cons_0 x_35 x_36))))
(assert (isnil_0 nil_0))
(assert (forall ((x_38 Nat_1) (x_39 list_0))
	(iscons_0 (cons_0 x_38 x_39))))
(assert (forall ((x_40 Nat_1) (x_41 list_0))
	(diseqlist_0 nil_0 (cons_0 x_40 x_41))))
(assert (forall ((x_42 Nat_1) (x_43 list_0))
	(diseqlist_0 (cons_0 x_42 x_43) nil_0)))
(assert (forall ((x_44 Nat_1) (x_45 list_0) (x_46 Nat_1) (x_47 list_0))
	(=> (diseqNat_1 x_44 x_46)
	    (diseqlist_0 (cons_0 x_44 x_45) (cons_0 x_46 x_47)))))
(assert (forall ((x_44 Nat_1) (x_45 list_0) (x_46 Nat_1) (x_47 list_0))
	(=> (diseqlist_0 x_45 x_47)
	    (diseqlist_0 (cons_0 x_44 x_45) (cons_0 x_46 x_47)))))
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_1 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_49 Nat_0))
	(p_1 x_49 (succ_0 x_49))))
(assert (iszero_0 zero_0))
(assert (forall ((x_51 Nat_0))
	(issucc_0 (succ_0 x_51))))
(assert (forall ((x_52 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_52))))
(assert (forall ((x_53 Nat_0))
	(diseqNat_0 (succ_0 x_53) zero_0)))
(assert (forall ((x_54 Nat_0) (x_55 Nat_0))
	(=> (diseqNat_0 x_54 x_55)
	    (diseqNat_0 (succ_0 x_54) (succ_0 x_55)))))
(declare-fun snoc_0 (list_0 Nat_1 list_0) Bool)
(assert (forall ((x_9 list_0) (z_0 Nat_1) (ys_0 list_0) (x_0 Nat_1))
	(=> (snoc_0 x_9 x_0 ys_0)
	    (snoc_0 (cons_0 z_0 x_9) x_0 (cons_0 z_0 ys_0)))))
(assert (forall ((x_0 Nat_1))
	(snoc_0 (cons_0 x_0 nil_0) x_0 nil_0)))
(declare-fun rotate_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_11 list_0) (x_12 list_0) (z_2 Nat_1) (xs_0 list_0) (z_1 Nat_0))
	(=>	(and (snoc_0 x_12 z_2 xs_0)
			(rotate_0 x_11 z_1 x_12))
		(rotate_0 x_11 (succ_0 z_1) (cons_0 z_2 xs_0)))))
(assert (forall ((z_1 Nat_0))
	(rotate_0 nil_0 (succ_0 z_1) nil_0)))
(assert (forall ((x_15 list_0))
	(rotate_0 x_15 zero_0 x_15)))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_17 Nat_0) (z_3 Nat_0) (y_2 Nat_0))
	(=> (plus_0 x_17 z_3 y_2)
	    (plus_0 (succ_0 x_17) (succ_0 z_3) y_2))))
(assert (forall ((x_18 Nat_0))
	(plus_0 x_18 zero_0 x_18)))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_19 Nat_0) (x_20 Nat_0) (y_3 Nat_1) (l_0 list_0))
	(=>	(and (length_0 x_20 l_0)
			(plus_0 x_19 (succ_0 zero_0) x_20))
		(length_0 x_19 (cons_0 y_3 l_0)))))
(assert (length_0 zero_0 nil_0))
(assert (forall ((x_23 Nat_0) (x_24 Nat_0) (x_25 Nat_0) (x_26 Nat_0) (x_4 Nat_0) (y_4 Nat_0) (z_4 Nat_0))
	(=>	(and (diseqNat_0 x_24 x_26)
			(plus_0 x_23 y_4 z_4)
			(plus_0 x_24 x_4 x_23)
			(plus_0 x_25 x_4 y_4)
			(plus_0 x_26 x_25 z_4))
		false)))
(assert (forall ((x_27 Nat_0) (x_28 Nat_0) (x_5 Nat_0) (y_5 Nat_0))
	(=>	(and (diseqNat_0 x_27 x_28)
			(plus_0 x_27 x_5 y_5)
			(plus_0 x_28 y_5 x_5))
		false)))
(assert (forall ((x_29 Nat_0) (x_6 Nat_0))
	(=>	(and (diseqNat_0 x_29 x_6)
			(plus_0 x_29 x_6 zero_0))
		false)))
(assert (forall ((x_30 Nat_0) (x_7 Nat_0))
	(=>	(and (diseqNat_0 x_30 x_7)
			(plus_0 x_30 zero_0 x_7))
		false)))
(assert (forall ((x_31 Nat_0) (x_32 list_0) (xs_1 list_0))
	(=>	(and (diseqlist_0 x_32 xs_1)
			(length_0 x_31 xs_1)
			(rotate_0 x_32 x_31 xs_1))
		false)))
(check-sat)
