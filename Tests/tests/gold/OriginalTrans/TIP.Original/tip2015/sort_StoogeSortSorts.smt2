(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_5 ) (Z_6 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_77 Nat_0))
	(unS_1 x_77 (Z_6 x_77))))
(assert (isZ_2 Z_5))
(assert (forall ((x_79 Nat_0))
	(isZ_3 (Z_6 x_79))))
(assert (forall ((x_80 Nat_0))
	(diseqNat_0 Z_5 (Z_6 x_80))))
(assert (forall ((x_81 Nat_0))
	(diseqNat_0 (Z_6 x_81) Z_5)))
(assert (forall ((x_82 Nat_0) (x_83 Nat_0))
	(=> (diseqNat_0 x_82 x_83)
	    (diseqNat_0 (Z_6 x_82) (Z_6 x_83)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_11 Nat_0))
	(add_0 y_11 Z_5 y_11)))
(assert (forall ((r_0 Nat_0) (x_70 Nat_0) (y_11 Nat_0))
	(=> (add_0 r_0 x_70 y_11)
	    (add_0 (Z_6 r_0) (Z_6 x_70) y_11))))
(assert (forall ((y_11 Nat_0))
	(minus_0 Z_5 Z_5 y_11)))
(assert (forall ((r_0 Nat_0) (x_70 Nat_0) (y_11 Nat_0))
	(=> (minus_0 r_0 x_70 y_11)
	    (minus_0 (Z_6 r_0) (Z_6 x_70) y_11))))
(assert (forall ((y_11 Nat_0))
	(le_0 Z_5 y_11)))
(assert (forall ((x_70 Nat_0) (y_11 Nat_0))
	(=> (le_0 x_70 y_11)
	    (le_0 (Z_6 x_70) (Z_6 y_11)))))
(assert (forall ((y_11 Nat_0))
	(ge_0 y_11 Z_5)))
(assert (forall ((x_70 Nat_0) (y_11 Nat_0))
	(=> (ge_0 x_70 y_11)
	    (ge_0 (Z_6 x_70) (Z_6 y_11)))))
(assert (forall ((y_11 Nat_0))
	(lt_0 Z_5 (Z_6 y_11))))
(assert (forall ((x_70 Nat_0) (y_11 Nat_0))
	(=> (lt_0 x_70 y_11)
	    (lt_0 (Z_6 x_70) (Z_6 y_11)))))
(assert (forall ((y_11 Nat_0))
	(gt_0 (Z_6 y_11) Z_5)))
(assert (forall ((x_70 Nat_0) (y_11 Nat_0))
	(=> (gt_0 x_70 y_11)
	    (gt_0 (Z_6 x_70) (Z_6 y_11)))))
(assert (forall ((y_11 Nat_0))
	(mult_0 Z_5 Z_5 y_11)))
(assert (forall ((r_0 Nat_0) (x_70 Nat_0) (y_11 Nat_0) (z_7 Nat_0))
	(=>	(and (mult_0 r_0 x_70 y_11)
			(add_0 z_7 r_0 y_11))
		(mult_0 z_7 (Z_6 x_70) y_11))))
(assert (forall ((x_70 Nat_0) (y_11 Nat_0))
	(=> (lt_0 x_70 y_11)
	    (div_0 Z_5 x_70 y_11))))
(assert (forall ((r_0 Nat_0) (x_70 Nat_0) (y_11 Nat_0) (z_7 Nat_0))
	(=>	(and (ge_0 x_70 y_11)
			(minus_0 z_7 x_70 y_11)
			(div_0 r_0 z_7 y_11))
		(div_0 (Z_6 r_0) x_70 y_11))))
(assert (forall ((x_70 Nat_0) (y_11 Nat_0))
	(=> (lt_0 x_70 y_11)
	    (mod_0 x_70 x_70 y_11))))
(assert (forall ((r_0 Nat_0) (x_70 Nat_0) (y_11 Nat_0) (z_7 Nat_0))
	(=>	(and (ge_0 x_70 y_11)
			(minus_0 z_7 x_70 y_11)
			(mod_0 r_0 z_7 y_11))
		(mod_0 r_0 x_70 y_11))))
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
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_87 Nat_0) (x_88 list_0))
	(head_1 x_87 (cons_0 x_87 x_88))))
(assert (forall ((x_87 Nat_0) (x_88 list_0))
	(tail_1 x_88 (cons_0 x_87 x_88))))
(assert (isnil_0 nil_0))
(assert (forall ((x_90 Nat_0) (x_91 list_0))
	(iscons_0 (cons_0 x_90 x_91))))
(assert (forall ((x_92 Nat_0) (x_93 list_0))
	(diseqlist_0 nil_0 (cons_0 x_92 x_93))))
(assert (forall ((x_94 Nat_0) (x_95 list_0))
	(diseqlist_0 (cons_0 x_94 x_95) nil_0)))
(assert (forall ((x_96 Nat_0) (x_97 list_0) (x_98 Nat_0) (x_99 list_0))
	(=> (diseqNat_0 x_96 x_98)
	    (diseqlist_0 (cons_0 x_96 x_97) (cons_0 x_98 x_99)))))
(assert (forall ((x_96 Nat_0) (x_97 list_0) (x_98 Nat_0) (x_99 list_0))
	(=> (diseqlist_0 x_97 x_99)
	    (diseqlist_0 (cons_0 x_96 x_97) (cons_0 x_98 x_99)))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 list_0) (projpair_1 list_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (list_0 pair_0) Bool)
(declare-fun projpair_3 (list_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_100 list_0) (x_101 list_0))
	(projpair_2 x_100 (pair_1 x_100 x_101))))
(assert (forall ((x_100 list_0) (x_101 list_0))
	(projpair_3 x_101 (pair_1 x_100 x_101))))
(assert (forall ((x_103 list_0) (x_104 list_0))
	(ispair_0 (pair_1 x_103 x_104))))
(assert (forall ((x_105 list_0) (x_106 list_0) (x_107 list_0) (x_108 list_0))
	(=> (diseqlist_0 x_105 x_107)
	    (diseqpair_0 (pair_1 x_105 x_106) (pair_1 x_107 x_108)))))
(assert (forall ((x_105 list_0) (x_106 list_0) (x_107 list_0) (x_108 list_0))
	(=> (diseqlist_0 x_106 x_108)
	    (diseqpair_0 (pair_1 x_105 x_106) (pair_1 x_107 x_108)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_0 Nat_0) (y_0 list_0))
	(=> (le_0 x_0 Z_5)
	    (take_0 nil_0 x_0 y_0))))
(assert (forall ((x_71 Nat_0) (x_20 list_0) (z_0 Nat_0) (xs_0 list_0) (x_0 Nat_0))
	(=>	(and (gt_0 x_0 Z_5)
			(take_0 x_20 x_71 xs_0)
			(minus_0 x_71 x_0 (Z_6 Z_5)))
		(take_0 (cons_0 z_0 x_20) x_0 (cons_0 z_0 xs_0)))))
(assert (forall ((x_0 Nat_0) (y_0 list_0))
	(=> (le_0 x_0 Z_5)
	    (take_0 nil_0 x_0 y_0))))
(assert (forall ((x_0 Nat_0))
	(=> (gt_0 x_0 Z_5)
	    (take_0 nil_0 x_0 nil_0))))
(declare-fun sort_0 (list_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_1 Nat_0) (y_1 Nat_0))
	(=> (le_0 x_1 y_1)
	    (sort_0 (cons_0 x_1 (cons_0 y_1 nil_0)) x_1 y_1))))
(assert (forall ((x_1 Nat_0) (y_1 Nat_0))
	(=> (gt_0 x_1 y_1)
	    (sort_0 (cons_0 y_1 (cons_0 x_1 nil_0)) x_1 y_1))))
(declare-fun ordered_0 (Bool_0 list_0) Bool)
(assert (forall ((x_25 Bool_0) (y_3 Nat_0) (xs_1 list_0) (y_2 Nat_0))
	(=>	(and (le_0 y_2 y_3)
			(ordered_0 x_25 (cons_0 y_3 xs_1)))
		(ordered_0 x_25 (cons_0 y_2 (cons_0 y_3 xs_1))))))
(assert (forall ((y_3 Nat_0) (xs_1 list_0) (y_2 Nat_0))
	(=> (gt_0 y_2 y_3)
	    (ordered_0 false_0 (cons_0 y_2 (cons_0 y_3 xs_1))))))
(assert (forall ((y_2 Nat_0))
	(ordered_0 true_0 (cons_0 y_2 nil_0))))
(assert (ordered_0 true_0 nil_0))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_30 Nat_0) (x_31 Nat_0) (y_4 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_31 l_0)
			(add_0 x_30 (Z_6 Z_5) x_31))
		(length_0 x_30 (cons_0 y_4 l_0)))))
(assert (length_0 Z_5 nil_0))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_33 list_0) (x_4 Nat_0))
	(=> (le_0 x_4 Z_5)
	    (drop_0 x_33 x_4 x_33))))
(assert (forall ((x_73 Nat_0) (x_34 list_0) (z_2 Nat_0) (xs_2 list_0) (x_4 Nat_0))
	(=>	(and (gt_0 x_4 Z_5)
			(drop_0 x_34 x_73 xs_2)
			(minus_0 x_73 x_4 (Z_6 Z_5)))
		(drop_0 x_34 x_4 (cons_0 z_2 xs_2)))))
(assert (forall ((x_36 list_0) (x_4 Nat_0))
	(=> (le_0 x_4 Z_5)
	    (drop_0 x_36 x_4 x_36))))
(assert (forall ((x_4 Nat_0))
	(=> (gt_0 x_4 Z_5)
	    (drop_0 nil_0 x_4 nil_0))))
(declare-fun splitAt_0 (pair_0 Nat_0 list_0) Bool)
(assert (forall ((x_39 list_0) (x_40 list_0) (x_5 Nat_0) (y_6 list_0))
	(=>	(and (take_0 x_39 x_5 y_6)
			(drop_0 x_40 x_5 y_6))
		(splitAt_0 (pair_1 x_39 x_40) x_5 y_6))))
(declare-fun x_6 (list_0 list_0 list_0) Bool)
(assert (forall ((x_42 list_0) (z_3 Nat_0) (xs_3 list_0) (y_7 list_0))
	(=> (x_6 x_42 xs_3 y_7)
	    (x_6 (cons_0 z_3 x_42) (cons_0 z_3 xs_3) y_7))))
(assert (forall ((x_43 list_0))
	(x_6 x_43 nil_0 x_43)))
(declare-fun reverse_0 (list_0 list_0) Bool)
(assert (forall ((x_44 list_0) (x_45 list_0) (y_8 Nat_0) (xs_4 list_0))
	(=>	(and (reverse_0 x_45 xs_4)
			(x_6 x_44 x_45 (cons_0 y_8 nil_0)))
		(reverse_0 x_44 (cons_0 y_8 xs_4)))))
(assert (reverse_0 nil_0 nil_0))
(declare-fun stoogesort_0 (list_0 list_0) Bool)
(declare-fun stoogesort_1 (list_0 list_0) Bool)
(declare-fun stoogesort_2 (list_0 list_0) Bool)
(assert (forall ((x_74 Nat_0) (x_51 list_0) (x_52 list_0) (x_53 list_0) (x_48 Nat_0) (x_49 list_0) (ys_0 list_0) (zs_0 list_0) (x_12 list_0))
	(=>	(and (stoogesort_1 x_52 zs_0)
			(reverse_0 x_53 ys_0)
			(x_6 x_51 x_52 x_53)
			(length_0 x_48 x_12)
			(reverse_0 x_49 x_12)
			(splitAt_0 (pair_1 ys_0 zs_0) x_74 x_49)
			(div_0 x_74 x_48 (Z_6 (Z_6 (Z_6 Z_5)))))
		(stoogesort_0 x_51 x_12))))
(assert (forall ((x_55 list_0) (x_56 list_0) (x_57 list_0) (x_15 Nat_0) (x_16 list_0) (y_10 Nat_0) (y_9 Nat_0))
	(=>	(and (stoogesort_0 x_56 (cons_0 y_9 (cons_0 y_10 (cons_0 x_15 x_16))))
			(stoogesort_2 x_57 x_56)
			(stoogesort_0 x_55 x_57))
		(stoogesort_1 x_55 (cons_0 y_9 (cons_0 y_10 (cons_0 x_15 x_16)))))))
(assert (forall ((x_59 list_0) (y_10 Nat_0) (y_9 Nat_0))
	(=> (sort_0 x_59 y_9 y_10)
	    (stoogesort_1 x_59 (cons_0 y_9 (cons_0 y_10 nil_0))))))
(assert (forall ((y_9 Nat_0))
	(stoogesort_1 (cons_0 y_9 nil_0) (cons_0 y_9 nil_0))))
(assert (stoogesort_1 nil_0 nil_0))
(assert (forall ((x_75 Nat_0) (x_65 list_0) (x_66 list_0) (x_63 Nat_0) (ys_1 list_0) (zs_1 list_0) (x_17 list_0))
	(=>	(and (stoogesort_1 x_66 zs_1)
			(x_6 x_65 ys_1 x_66)
			(length_0 x_63 x_17)
			(splitAt_0 (pair_1 ys_1 zs_1) x_75 x_17)
			(div_0 x_75 x_63 (Z_6 (Z_6 (Z_6 Z_5)))))
		(stoogesort_2 x_65 x_17))))
(assert (forall ((x_68 list_0) (x_69 Bool_0) (xs_5 list_0))
	(=>	(and (diseqBool_0 x_69 true_0)
			(stoogesort_1 x_68 xs_5)
			(ordered_0 x_69 x_68))
		false)))
(check-sat)