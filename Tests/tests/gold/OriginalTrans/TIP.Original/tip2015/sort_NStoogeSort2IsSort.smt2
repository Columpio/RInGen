(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_5 ) (Z_6 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_98 Nat_0))
	(unS_1 x_98 (Z_6 x_98))))
(assert (isZ_2 Z_5))
(assert (forall ((x_100 Nat_0))
	(isZ_3 (Z_6 x_100))))
(assert (forall ((x_101 Nat_0))
	(diseqNat_0 Z_5 (Z_6 x_101))))
(assert (forall ((x_102 Nat_0))
	(diseqNat_0 (Z_6 x_102) Z_5)))
(assert (forall ((x_103 Nat_0) (x_104 Nat_0))
	(=> (diseqNat_0 x_103 x_104)
	    (diseqNat_0 (Z_6 x_103) (Z_6 x_104)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_10 Nat_0))
	(add_0 y_10 Z_5 y_10)))
(assert (forall ((r_0 Nat_0) (x_89 Nat_0) (y_10 Nat_0))
	(=> (add_0 r_0 x_89 y_10)
	    (add_0 (Z_6 r_0) (Z_6 x_89) y_10))))
(assert (forall ((y_10 Nat_0))
	(minus_0 Z_5 Z_5 y_10)))
(assert (forall ((r_0 Nat_0) (x_89 Nat_0) (y_10 Nat_0))
	(=> (minus_0 r_0 x_89 y_10)
	    (minus_0 (Z_6 r_0) (Z_6 x_89) y_10))))
(assert (forall ((y_10 Nat_0))
	(le_0 Z_5 y_10)))
(assert (forall ((x_89 Nat_0) (y_10 Nat_0))
	(=> (le_0 x_89 y_10)
	    (le_0 (Z_6 x_89) (Z_6 y_10)))))
(assert (forall ((y_10 Nat_0))
	(ge_0 y_10 Z_5)))
(assert (forall ((x_89 Nat_0) (y_10 Nat_0))
	(=> (ge_0 x_89 y_10)
	    (ge_0 (Z_6 x_89) (Z_6 y_10)))))
(assert (forall ((y_10 Nat_0))
	(lt_0 Z_5 (Z_6 y_10))))
(assert (forall ((x_89 Nat_0) (y_10 Nat_0))
	(=> (lt_0 x_89 y_10)
	    (lt_0 (Z_6 x_89) (Z_6 y_10)))))
(assert (forall ((y_10 Nat_0))
	(gt_0 (Z_6 y_10) Z_5)))
(assert (forall ((x_89 Nat_0) (y_10 Nat_0))
	(=> (gt_0 x_89 y_10)
	    (gt_0 (Z_6 x_89) (Z_6 y_10)))))
(assert (forall ((y_10 Nat_0))
	(mult_0 Z_5 Z_5 y_10)))
(assert (forall ((r_0 Nat_0) (x_89 Nat_0) (y_10 Nat_0) (z_7 Nat_0))
	(=>	(and (mult_0 r_0 x_89 y_10)
			(add_0 z_7 r_0 y_10))
		(mult_0 z_7 (Z_6 x_89) y_10))))
(assert (forall ((x_89 Nat_0) (y_10 Nat_0))
	(=> (lt_0 x_89 y_10)
	    (div_0 Z_5 x_89 y_10))))
(assert (forall ((r_0 Nat_0) (x_89 Nat_0) (y_10 Nat_0) (z_7 Nat_0))
	(=>	(and (ge_0 x_89 y_10)
			(minus_0 z_7 x_89 y_10)
			(div_0 r_0 z_7 y_10))
		(div_0 (Z_6 r_0) x_89 y_10))))
(assert (forall ((x_89 Nat_0) (y_10 Nat_0))
	(=> (lt_0 x_89 y_10)
	    (mod_0 x_89 x_89 y_10))))
(assert (forall ((r_0 Nat_0) (x_89 Nat_0) (y_10 Nat_0) (z_7 Nat_0))
	(=>	(and (ge_0 x_89 y_10)
			(minus_0 z_7 x_89 y_10)
			(mod_0 r_0 z_7 y_10))
		(mod_0 r_0 x_89 y_10))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_106 Nat_0) (x_107 list_0))
	(head_1 x_106 (cons_0 x_106 x_107))))
(assert (forall ((x_106 Nat_0) (x_107 list_0))
	(tail_1 x_107 (cons_0 x_106 x_107))))
(assert (isnil_0 nil_0))
(assert (forall ((x_109 Nat_0) (x_110 list_0))
	(iscons_0 (cons_0 x_109 x_110))))
(assert (forall ((x_111 Nat_0) (x_112 list_0))
	(diseqlist_0 nil_0 (cons_0 x_111 x_112))))
(assert (forall ((x_113 Nat_0) (x_114 list_0))
	(diseqlist_0 (cons_0 x_113 x_114) nil_0)))
(assert (forall ((x_115 Nat_0) (x_116 list_0) (x_117 Nat_0) (x_118 list_0))
	(=> (diseqNat_0 x_115 x_117)
	    (diseqlist_0 (cons_0 x_115 x_116) (cons_0 x_117 x_118)))))
(assert (forall ((x_115 Nat_0) (x_116 list_0) (x_117 Nat_0) (x_118 list_0))
	(=> (diseqlist_0 x_116 x_118)
	    (diseqlist_0 (cons_0 x_115 x_116) (cons_0 x_117 x_118)))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 list_0) (projpair_1 list_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (list_0 pair_0) Bool)
(declare-fun projpair_3 (list_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_119 list_0) (x_120 list_0))
	(projpair_2 x_119 (pair_1 x_119 x_120))))
(assert (forall ((x_119 list_0) (x_120 list_0))
	(projpair_3 x_120 (pair_1 x_119 x_120))))
(assert (forall ((x_122 list_0) (x_123 list_0))
	(ispair_0 (pair_1 x_122 x_123))))
(assert (forall ((x_124 list_0) (x_125 list_0) (x_126 list_0) (x_127 list_0))
	(=> (diseqlist_0 x_124 x_126)
	    (diseqpair_0 (pair_1 x_124 x_125) (pair_1 x_126 x_127)))))
(assert (forall ((x_124 list_0) (x_125 list_0) (x_126 list_0) (x_127 list_0))
	(=> (diseqlist_0 x_125 x_127)
	    (diseqpair_0 (pair_1 x_124 x_125) (pair_1 x_126 x_127)))))
(declare-fun twoThirds_0 (Nat_0 Nat_0) Bool)
(assert (twoThirds_0 (Z_6 Z_5) (Z_6 (Z_6 Z_5))))
(assert (=> (diseqNat_0 (Z_6 Z_5) (Z_6 (Z_6 Z_5)))
	    (twoThirds_0 (Z_6 Z_5) (Z_6 Z_5))))
(assert (twoThirds_0 (Z_6 Z_5) (Z_6 (Z_6 Z_5))))
(assert (=>	(and (diseqNat_0 Z_5 (Z_6 (Z_6 Z_5)))
			(diseqNat_0 Z_5 (Z_6 Z_5)))
		(twoThirds_0 Z_5 Z_5)))
(assert (twoThirds_0 (Z_6 Z_5) (Z_6 (Z_6 Z_5))))
(assert (=> (diseqNat_0 (Z_6 Z_5) (Z_6 (Z_6 Z_5)))
	    (twoThirds_0 (Z_6 Z_5) (Z_6 Z_5))))
(assert (twoThirds_0 (Z_6 Z_5) (Z_6 (Z_6 Z_5))))
(assert (forall ((x_91 Nat_0) (x_27 Nat_0) (x_28 Nat_0) (x_0 Nat_0))
	(=>	(and (diseqNat_0 x_0 (Z_6 (Z_6 Z_5)))
			(diseqNat_0 x_0 (Z_6 Z_5))
			(diseqNat_0 x_0 Z_5)
			(twoThirds_0 x_28 x_91)
			(minus_0 x_91 x_0 (Z_6 (Z_6 (Z_6 Z_5))))
			(add_0 x_27 (Z_6 (Z_6 Z_5)) x_28))
		(twoThirds_0 x_27 x_0))))
(declare-fun third_0 (Nat_0 Nat_0) Bool)
(assert (third_0 Z_5 (Z_6 (Z_6 Z_5))))
(assert (=> (diseqNat_0 (Z_6 Z_5) (Z_6 (Z_6 Z_5)))
	    (third_0 Z_5 (Z_6 Z_5))))
(assert (third_0 Z_5 (Z_6 (Z_6 Z_5))))
(assert (=>	(and (diseqNat_0 Z_5 (Z_6 (Z_6 Z_5)))
			(diseqNat_0 Z_5 (Z_6 Z_5)))
		(third_0 Z_5 Z_5)))
(assert (third_0 Z_5 (Z_6 (Z_6 Z_5))))
(assert (=> (diseqNat_0 (Z_6 Z_5) (Z_6 (Z_6 Z_5)))
	    (third_0 Z_5 (Z_6 Z_5))))
(assert (third_0 Z_5 (Z_6 (Z_6 Z_5))))
(assert (forall ((x_93 Nat_0) (x_36 Nat_0) (x_37 Nat_0) (x_1 Nat_0))
	(=>	(and (diseqNat_0 x_1 (Z_6 (Z_6 Z_5)))
			(diseqNat_0 x_1 (Z_6 Z_5))
			(diseqNat_0 x_1 Z_5)
			(third_0 x_37 x_93)
			(minus_0 x_93 x_1 (Z_6 (Z_6 (Z_6 Z_5))))
			(add_0 x_36 (Z_6 Z_5) x_37))
		(third_0 x_36 x_1))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_2 Nat_0) (y_0 list_0))
	(=> (le_0 x_2 Z_5)
	    (take_0 nil_0 x_2 y_0))))
(assert (forall ((x_94 Nat_0) (x_40 list_0) (z_0 Nat_0) (xs_0 list_0) (x_2 Nat_0))
	(=>	(and (gt_0 x_2 Z_5)
			(take_0 x_40 x_94 xs_0)
			(minus_0 x_94 x_2 (Z_6 Z_5)))
		(take_0 (cons_0 z_0 x_40) x_2 (cons_0 z_0 xs_0)))))
(assert (forall ((x_2 Nat_0) (y_0 list_0))
	(=> (le_0 x_2 Z_5)
	    (take_0 nil_0 x_2 y_0))))
(assert (forall ((x_2 Nat_0))
	(=> (gt_0 x_2 Z_5)
	    (take_0 nil_0 x_2 nil_0))))
(declare-fun sort_0 (list_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_3 Nat_0) (y_1 Nat_0))
	(=> (le_0 x_3 y_1)
	    (sort_0 (cons_0 x_3 (cons_0 y_1 nil_0)) x_3 y_1))))
(assert (forall ((x_3 Nat_0) (y_1 Nat_0))
	(=> (gt_0 x_3 y_1)
	    (sort_0 (cons_0 y_1 (cons_0 x_3 nil_0)) x_3 y_1))))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_45 Nat_0) (x_46 Nat_0) (y_2 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_46 l_0)
			(add_0 x_45 (Z_6 Z_5) x_46))
		(length_0 x_45 (cons_0 y_2 l_0)))))
(assert (length_0 Z_5 nil_0))
(declare-fun insert_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((z_1 Nat_0) (xs_1 list_0) (x_5 Nat_0))
	(=> (le_0 x_5 z_1)
	    (insert_0 (cons_0 x_5 (cons_0 z_1 xs_1)) x_5 (cons_0 z_1 xs_1)))))
(assert (forall ((x_50 list_0) (z_1 Nat_0) (xs_1 list_0) (x_5 Nat_0))
	(=>	(and (gt_0 x_5 z_1)
			(insert_0 x_50 x_5 xs_1))
		(insert_0 (cons_0 z_1 x_50) x_5 (cons_0 z_1 xs_1)))))
(assert (forall ((x_5 Nat_0))
	(insert_0 (cons_0 x_5 nil_0) x_5 nil_0)))
(declare-fun isort_0 (list_0 list_0) Bool)
(assert (forall ((x_52 list_0) (x_53 list_0) (y_4 Nat_0) (xs_2 list_0))
	(=>	(and (isort_0 x_53 xs_2)
			(insert_0 x_52 y_4 x_53))
		(isort_0 x_52 (cons_0 y_4 xs_2)))))
(assert (isort_0 nil_0 nil_0))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_56 list_0) (x_7 Nat_0))
	(=> (le_0 x_7 Z_5)
	    (drop_0 x_56 x_7 x_56))))
(assert (forall ((x_96 Nat_0) (x_57 list_0) (z_2 Nat_0) (xs_3 list_0) (x_7 Nat_0))
	(=>	(and (gt_0 x_7 Z_5)
			(drop_0 x_57 x_96 xs_3)
			(minus_0 x_96 x_7 (Z_6 Z_5)))
		(drop_0 x_57 x_7 (cons_0 z_2 xs_3)))))
(assert (forall ((x_59 list_0) (x_7 Nat_0))
	(=> (le_0 x_7 Z_5)
	    (drop_0 x_59 x_7 x_59))))
(assert (forall ((x_7 Nat_0))
	(=> (gt_0 x_7 Z_5)
	    (drop_0 nil_0 x_7 nil_0))))
(declare-fun splitAt_0 (pair_0 Nat_0 list_0) Bool)
(assert (forall ((x_62 list_0) (x_63 list_0) (x_8 Nat_0) (y_6 list_0))
	(=>	(and (take_0 x_62 x_8 y_6)
			(drop_0 x_63 x_8 y_6))
		(splitAt_0 (pair_1 x_62 x_63) x_8 y_6))))
(declare-fun x_9 (list_0 list_0 list_0) Bool)
(assert (forall ((x_65 list_0) (z_3 Nat_0) (xs_4 list_0) (y_7 list_0))
	(=> (x_9 x_65 xs_4 y_7)
	    (x_9 (cons_0 z_3 x_65) (cons_0 z_3 xs_4) y_7))))
(assert (forall ((x_66 list_0))
	(x_9 x_66 nil_0 x_66)))
(declare-fun nstoogesort_0 (list_0 list_0) Bool)
(declare-fun nstoogesort_1 (list_0 list_0) Bool)
(declare-fun nstoogesort_2 (list_0 list_0) Bool)
(assert (forall ((x_70 list_0) (x_71 list_0) (x_67 Nat_0) (x_68 Nat_0) (ys_0 list_0) (zs_0 list_0) (x_14 list_0))
	(=>	(and (nstoogesort_1 x_71 ys_0)
			(x_9 x_70 x_71 zs_0)
			(length_0 x_67 x_14)
			(twoThirds_0 x_68 x_67)
			(splitAt_0 (pair_1 ys_0 zs_0) x_68 x_14))
		(nstoogesort_0 x_70 x_14))))
(assert (forall ((x_73 list_0) (x_74 list_0) (x_75 list_0) (x_17 Nat_0) (x_18 list_0) (y_9 Nat_0) (y_8 Nat_0))
	(=>	(and (nstoogesort_0 x_74 (cons_0 y_8 (cons_0 y_9 (cons_0 x_17 x_18))))
			(nstoogesort_2 x_75 x_74)
			(nstoogesort_0 x_73 x_75))
		(nstoogesort_1 x_73 (cons_0 y_8 (cons_0 y_9 (cons_0 x_17 x_18)))))))
(assert (forall ((x_77 list_0) (y_9 Nat_0) (y_8 Nat_0))
	(=> (sort_0 x_77 y_8 y_9)
	    (nstoogesort_1 x_77 (cons_0 y_8 (cons_0 y_9 nil_0))))))
(assert (forall ((y_8 Nat_0))
	(nstoogesort_1 (cons_0 y_8 nil_0) (cons_0 y_8 nil_0))))
(assert (nstoogesort_1 nil_0 nil_0))
(assert (forall ((x_84 list_0) (x_85 list_0) (x_81 Nat_0) (x_82 Nat_0) (ys_1 list_0) (zs_1 list_0) (x_19 list_0))
	(=>	(and (nstoogesort_1 x_85 zs_1)
			(x_9 x_84 ys_1 x_85)
			(length_0 x_81 x_19)
			(third_0 x_82 x_81)
			(splitAt_0 (pair_1 ys_1 zs_1) x_82 x_19))
		(nstoogesort_2 x_84 x_19))))
(assert (forall ((x_87 list_0) (x_88 list_0) (xs_5 list_0))
	(=>	(and (diseqlist_0 x_87 x_88)
			(nstoogesort_1 x_87 xs_5)
			(isort_0 x_88 xs_5))
		false)))
(check-sat)
