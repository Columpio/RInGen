(set-logic HORN)
(declare-datatypes ((Nat_1 0)) (((Z_11 ) (Z_12 (unS_0 Nat_1)))))
(declare-fun diseqNat_1 (Nat_1 Nat_1) Bool)
(declare-fun unS_1 (Nat_1 Nat_1) Bool)
(declare-fun isZ_2 (Nat_1) Bool)
(declare-fun isZ_3 (Nat_1) Bool)
(assert (forall ((x_95 Nat_1))
	(unS_1 x_95 (Z_12 x_95))))
(assert (isZ_2 Z_11))
(assert (forall ((x_97 Nat_1))
	(isZ_3 (Z_12 x_97))))
(assert (forall ((x_98 Nat_1))
	(diseqNat_1 Z_11 (Z_12 x_98))))
(assert (forall ((x_99 Nat_1))
	(diseqNat_1 (Z_12 x_99) Z_11)))
(assert (forall ((x_100 Nat_1) (x_101 Nat_1))
	(=> (diseqNat_1 x_100 x_101)
	    (diseqNat_1 (Z_12 x_100) (Z_12 x_101)))))
(declare-fun add_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun minus_1 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun le_0 (Nat_1 Nat_1) Bool)
(declare-fun ge_0 (Nat_1 Nat_1) Bool)
(declare-fun lt_0 (Nat_1 Nat_1) Bool)
(declare-fun gt_0 (Nat_1 Nat_1) Bool)
(declare-fun mult_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun div_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun mod_0 (Nat_1 Nat_1 Nat_1) Bool)
(assert (forall ((y_12 Nat_1))
	(add_0 y_12 Z_11 y_12)))
(assert (forall ((r_0 Nat_1) (x_71 Nat_1) (y_12 Nat_1))
	(=> (add_0 r_0 x_71 y_12)
	    (add_0 (Z_12 r_0) (Z_12 x_71) y_12))))
(assert (forall ((y_12 Nat_1))
	(minus_1 Z_11 Z_11 y_12)))
(assert (forall ((r_0 Nat_1) (x_71 Nat_1) (y_12 Nat_1))
	(=> (minus_1 r_0 x_71 y_12)
	    (minus_1 (Z_12 r_0) (Z_12 x_71) y_12))))
(assert (forall ((y_12 Nat_1))
	(le_0 Z_11 y_12)))
(assert (forall ((x_71 Nat_1) (y_12 Nat_1))
	(=> (le_0 x_71 y_12)
	    (le_0 (Z_12 x_71) (Z_12 y_12)))))
(assert (forall ((y_12 Nat_1))
	(ge_0 y_12 Z_11)))
(assert (forall ((x_71 Nat_1) (y_12 Nat_1))
	(=> (ge_0 x_71 y_12)
	    (ge_0 (Z_12 x_71) (Z_12 y_12)))))
(assert (forall ((y_12 Nat_1))
	(lt_0 Z_11 (Z_12 y_12))))
(assert (forall ((x_71 Nat_1) (y_12 Nat_1))
	(=> (lt_0 x_71 y_12)
	    (lt_0 (Z_12 x_71) (Z_12 y_12)))))
(assert (forall ((y_12 Nat_1))
	(gt_0 (Z_12 y_12) Z_11)))
(assert (forall ((x_71 Nat_1) (y_12 Nat_1))
	(=> (gt_0 x_71 y_12)
	    (gt_0 (Z_12 x_71) (Z_12 y_12)))))
(assert (forall ((y_12 Nat_1))
	(mult_0 Z_11 Z_11 y_12)))
(assert (forall ((r_0 Nat_1) (x_71 Nat_1) (y_12 Nat_1) (z_13 Nat_1))
	(=>	(and (mult_0 r_0 x_71 y_12)
			(add_0 z_13 r_0 y_12))
		(mult_0 z_13 (Z_12 x_71) y_12))))
(assert (forall ((x_71 Nat_1) (y_12 Nat_1))
	(=> (lt_0 x_71 y_12)
	    (div_0 Z_11 x_71 y_12))))
(assert (forall ((r_0 Nat_1) (x_71 Nat_1) (y_12 Nat_1) (z_13 Nat_1))
	(=>	(and (ge_0 x_71 y_12)
			(minus_1 z_13 x_71 y_12)
			(div_0 r_0 z_13 y_12))
		(div_0 (Z_12 r_0) x_71 y_12))))
(assert (forall ((x_71 Nat_1) (y_12 Nat_1))
	(=> (lt_0 x_71 y_12)
	    (mod_0 x_71 x_71 y_12))))
(assert (forall ((r_0 Nat_1) (x_71 Nat_1) (y_12 Nat_1) (z_13 Nat_1))
	(=>	(and (ge_0 x_71 y_12)
			(minus_1 z_13 x_71 y_12)
			(mod_0 r_0 z_13 y_12))
		(mod_0 r_0 x_71 y_12))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_1) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_1 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_73 Nat_1) (x_74 list_0))
	(head_1 x_73 (cons_0 x_73 x_74))))
(assert (forall ((x_73 Nat_1) (x_74 list_0))
	(tail_1 x_74 (cons_0 x_73 x_74))))
(assert (isnil_0 nil_0))
(assert (forall ((x_76 Nat_1) (x_77 list_0))
	(iscons_0 (cons_0 x_76 x_77))))
(assert (forall ((x_78 Nat_1) (x_79 list_0))
	(diseqlist_0 nil_0 (cons_0 x_78 x_79))))
(assert (forall ((x_80 Nat_1) (x_81 list_0))
	(diseqlist_0 (cons_0 x_80 x_81) nil_0)))
(assert (forall ((x_82 Nat_1) (x_83 list_0) (x_84 Nat_1) (x_85 list_0))
	(=> (diseqNat_1 x_82 x_84)
	    (diseqlist_0 (cons_0 x_82 x_83) (cons_0 x_84 x_85)))))
(assert (forall ((x_82 Nat_1) (x_83 list_0) (x_84 Nat_1) (x_85 list_0))
	(=> (diseqlist_0 x_83 x_85)
	    (diseqlist_0 (cons_0 x_82 x_83) (cons_0 x_84 x_85)))))
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_1 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_87 Nat_0))
	(p_1 x_87 (succ_0 x_87))))
(assert (iszero_0 zero_0))
(assert (forall ((x_89 Nat_0))
	(issucc_0 (succ_0 x_89))))
(assert (forall ((x_90 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_90))))
(assert (forall ((x_91 Nat_0))
	(diseqNat_0 (succ_0 x_91) zero_0)))
(assert (forall ((x_92 Nat_0) (x_93 Nat_0))
	(=> (diseqNat_0 x_92 x_93)
	    (diseqNat_0 (succ_0 x_92) (succ_0 x_93)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_19 list_0) (z_1 Nat_1) (xs_0 list_0) (z_0 Nat_0))
	(=> (take_0 x_19 z_0 xs_0)
	    (take_0 (cons_0 z_1 x_19) (succ_0 z_0) (cons_0 z_1 xs_0)))))
(assert (forall ((z_0 Nat_0))
	(take_0 nil_0 (succ_0 z_0) nil_0)))
(assert (forall ((y_0 list_0))
	(take_0 nil_0 zero_0 y_0)))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_23 Nat_0) (z_2 Nat_0) (y_1 Nat_0))
	(=> (plus_0 x_23 z_2 y_1)
	    (plus_0 (succ_0 x_23) (succ_0 z_2) y_1))))
(assert (forall ((x_24 Nat_0))
	(plus_0 x_24 zero_0 x_24)))
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_25 Nat_0) (y_3 Nat_0) (z_3 Nat_0))
	(=> (minus_0 x_25 z_3 y_3)
	    (minus_0 x_25 (succ_0 z_3) (succ_0 y_3)))))
(assert (forall ((z_3 Nat_0))
	(minus_0 zero_0 (succ_0 z_3) zero_0)))
(assert (forall ((y_2 Nat_0))
	(minus_0 zero_0 zero_0 y_2)))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_29 Nat_0) (x_30 Nat_0) (y_4 Nat_1) (l_0 list_0))
	(=>	(and (length_0 x_30 l_0)
			(plus_0 x_29 (succ_0 zero_0) x_30))
		(length_0 x_29 (cons_0 y_4 l_0)))))
(assert (length_0 zero_0 nil_0))
(declare-fun go_0 (Nat_0 Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_33 Nat_0) (x_8 Nat_0) (x_7 Nat_0) (x_5 Nat_0))
	(=> (go_0 x_33 x_7 x_8 (succ_0 x_5))
	    (go_0 x_33 (succ_0 x_7) (succ_0 x_8) (succ_0 x_5)))))
(assert (forall ((x_35 Nat_0) (x_7 Nat_0) (x_5 Nat_0))
	(=> (go_0 x_35 x_7 x_5 (succ_0 x_5))
	    (go_0 x_35 (succ_0 x_7) zero_0 (succ_0 x_5)))))
(assert (forall ((x_37 Nat_0) (x_6 Nat_0) (x_5 Nat_0))
	(=> (minus_0 x_37 (succ_0 x_5) (succ_0 x_6))
	    (go_0 x_37 zero_0 (succ_0 x_6) (succ_0 x_5)))))
(assert (forall ((x_5 Nat_0))
	(go_0 zero_0 zero_0 zero_0 (succ_0 x_5))))
(assert (forall ((x_4 Nat_0) (y_5 Nat_0))
	(go_0 zero_0 x_4 y_5 zero_0)))
(declare-fun modstructural_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_41 Nat_0) (x_9 Nat_0) (y_6 Nat_0))
	(=> (go_0 x_41 x_9 zero_0 y_6)
	    (modstructural_0 x_41 x_9 y_6))))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_43 list_0) (z_6 Nat_1) (xs_1 list_0) (z_5 Nat_0))
	(=> (drop_0 x_43 z_5 xs_1)
	    (drop_0 x_43 (succ_0 z_5) (cons_0 z_6 xs_1)))))
(assert (forall ((z_5 Nat_0))
	(drop_0 nil_0 (succ_0 z_5) nil_0)))
(assert (forall ((x_46 list_0))
	(drop_0 x_46 zero_0 x_46)))
(declare-fun x_11 (list_0 list_0 list_0) Bool)
(assert (forall ((x_48 list_0) (z_7 Nat_1) (xs_2 list_0) (y_8 list_0))
	(=> (x_11 x_48 xs_2 y_8)
	    (x_11 (cons_0 z_7 x_48) (cons_0 z_7 xs_2) y_8))))
(assert (forall ((x_49 list_0))
	(x_11 x_49 nil_0 x_49)))
(declare-fun rotate_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_50 list_0) (x_51 list_0) (z_9 Nat_1) (xs_3 list_0) (z_8 Nat_0))
	(=>	(and (x_11 x_51 xs_3 (cons_0 z_9 nil_0))
			(rotate_0 x_50 z_8 x_51))
		(rotate_0 x_50 (succ_0 z_8) (cons_0 z_9 xs_3)))))
(assert (forall ((z_8 Nat_0))
	(rotate_0 nil_0 (succ_0 z_8) nil_0)))
(assert (forall ((x_54 list_0))
	(rotate_0 x_54 zero_0 x_54)))
(assert (forall ((x_55 Nat_0) (x_56 Nat_0) (x_57 Nat_0) (x_58 Nat_0) (x_14 Nat_0) (y_10 Nat_0) (z_10 Nat_0))
	(=>	(and (diseqNat_0 x_56 x_58)
			(plus_0 x_55 y_10 z_10)
			(plus_0 x_56 x_14 x_55)
			(plus_0 x_57 x_14 y_10)
			(plus_0 x_58 x_57 z_10))
		false)))
(assert (forall ((x_59 Nat_0) (x_60 Nat_0) (x_15 Nat_0) (y_11 Nat_0))
	(=>	(and (diseqNat_0 x_59 x_60)
			(plus_0 x_59 x_15 y_11)
			(plus_0 x_60 y_11 x_15))
		false)))
(assert (forall ((x_61 Nat_0) (x_16 Nat_0))
	(=>	(and (diseqNat_0 x_61 x_16)
			(plus_0 x_61 x_16 zero_0))
		false)))
(assert (forall ((x_62 Nat_0) (x_17 Nat_0))
	(=>	(and (diseqNat_0 x_62 x_17)
			(plus_0 x_62 zero_0 x_17))
		false)))
(assert (forall ((x_63 list_0) (x_64 Nat_0) (x_65 Nat_0) (x_66 list_0) (x_67 Nat_0) (x_68 Nat_0) (x_69 list_0) (x_70 list_0) (n_0 Nat_0) (xs_4 list_0))
	(=>	(and (diseqlist_0 x_63 x_70)
			(rotate_0 x_63 n_0 xs_4)
			(length_0 x_64 xs_4)
			(modstructural_0 x_65 n_0 x_64)
			(drop_0 x_66 x_65 xs_4)
			(length_0 x_67 xs_4)
			(modstructural_0 x_68 n_0 x_67)
			(take_0 x_69 x_68 xs_4)
			(x_11 x_70 x_66 x_69))
		false)))
(check-sat)