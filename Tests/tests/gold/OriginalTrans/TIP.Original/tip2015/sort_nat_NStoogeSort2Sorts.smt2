(set-logic HORN)
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
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_1 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_122 Nat_0))
	(p_1 x_122 (succ_0 x_122))))
(assert (iszero_0 zero_0))
(assert (forall ((x_124 Nat_0))
	(issucc_0 (succ_0 x_124))))
(assert (forall ((x_125 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_125))))
(assert (forall ((x_126 Nat_0))
	(diseqNat_0 (succ_0 x_126) zero_0)))
(assert (forall ((x_127 Nat_0) (x_128 Nat_0))
	(=> (diseqNat_0 x_127 x_128)
	    (diseqNat_0 (succ_0 x_127) (succ_0 x_128)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_130 Nat_0) (x_131 list_0))
	(head_1 x_130 (cons_0 x_130 x_131))))
(assert (forall ((x_130 Nat_0) (x_131 list_0))
	(tail_1 x_131 (cons_0 x_130 x_131))))
(assert (isnil_0 nil_0))
(assert (forall ((x_133 Nat_0) (x_134 list_0))
	(iscons_0 (cons_0 x_133 x_134))))
(assert (forall ((x_135 Nat_0) (x_136 list_0))
	(diseqlist_0 nil_0 (cons_0 x_135 x_136))))
(assert (forall ((x_137 Nat_0) (x_138 list_0))
	(diseqlist_0 (cons_0 x_137 x_138) nil_0)))
(assert (forall ((x_139 Nat_0) (x_140 list_0) (x_141 Nat_0) (x_142 list_0))
	(=> (diseqNat_0 x_139 x_141)
	    (diseqlist_0 (cons_0 x_139 x_140) (cons_0 x_141 x_142)))))
(assert (forall ((x_139 Nat_0) (x_140 list_0) (x_141 Nat_0) (x_142 list_0))
	(=> (diseqlist_0 x_140 x_142)
	    (diseqlist_0 (cons_0 x_139 x_140) (cons_0 x_141 x_142)))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 list_0) (projpair_1 list_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (list_0 pair_0) Bool)
(declare-fun projpair_3 (list_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_143 list_0) (x_144 list_0))
	(projpair_2 x_143 (pair_1 x_143 x_144))))
(assert (forall ((x_143 list_0) (x_144 list_0))
	(projpair_3 x_144 (pair_1 x_143 x_144))))
(assert (forall ((x_146 list_0) (x_147 list_0))
	(ispair_0 (pair_1 x_146 x_147))))
(assert (forall ((x_148 list_0) (x_149 list_0) (x_150 list_0) (x_151 list_0))
	(=> (diseqlist_0 x_148 x_150)
	    (diseqpair_0 (pair_1 x_148 x_149) (pair_1 x_150 x_151)))))
(assert (forall ((x_148 list_0) (x_149 list_0) (x_150 list_0) (x_151 list_0))
	(=> (diseqlist_0 x_149 x_151)
	    (diseqpair_0 (pair_1 x_148 x_149) (pair_1 x_150 x_151)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_28 list_0) (z_1 Nat_0) (xs_0 list_0) (z_0 Nat_0))
	(=> (take_0 x_28 z_0 xs_0)
	    (take_0 (cons_0 z_1 x_28) (succ_0 z_0) (cons_0 z_1 xs_0)))))
(assert (forall ((z_0 Nat_0))
	(take_0 nil_0 (succ_0 z_0) nil_0)))
(assert (forall ((y_0 list_0))
	(take_0 nil_0 zero_0 y_0)))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_32 Nat_0) (z_2 Nat_0) (y_1 Nat_0))
	(=> (plus_0 x_32 z_2 y_1)
	    (plus_0 (succ_0 x_32) (succ_0 z_2) y_1))))
(assert (forall ((x_33 Nat_0))
	(plus_0 x_33 zero_0 x_33)))
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_34 Nat_0) (y_3 Nat_0) (z_3 Nat_0))
	(=> (minus_0 x_34 z_3 y_3)
	    (minus_0 x_34 (succ_0 z_3) (succ_0 y_3)))))
(assert (forall ((z_3 Nat_0))
	(minus_0 zero_0 (succ_0 z_3) zero_0)))
(assert (forall ((y_2 Nat_0))
	(minus_0 zero_0 zero_0 y_2)))
(declare-fun third_0 (Nat_0 Nat_0) Bool)
(assert (third_0 zero_0 (succ_0 (succ_0 zero_0))))
(assert (=> (diseqNat_0 (succ_0 zero_0) (succ_0 (succ_0 zero_0)))
	    (third_0 zero_0 (succ_0 zero_0))))
(assert (third_0 zero_0 (succ_0 (succ_0 zero_0))))
(assert (forall ((x_41 Nat_0) (x_42 Nat_0) (x_43 Nat_0) (y_4 Nat_0))
	(=>	(and (diseqNat_0 (succ_0 y_4) (succ_0 (succ_0 zero_0)))
			(diseqNat_0 (succ_0 y_4) (succ_0 zero_0))
			(minus_0 x_42 (succ_0 y_4) (succ_0 (succ_0 (succ_0 zero_0))))
			(third_0 x_43 x_42)
			(plus_0 x_41 (succ_0 zero_0) x_43))
		(third_0 x_41 (succ_0 y_4)))))
(assert (third_0 zero_0 (succ_0 (succ_0 zero_0))))
(assert (=> (diseqNat_0 (succ_0 zero_0) (succ_0 (succ_0 zero_0)))
	    (third_0 zero_0 (succ_0 zero_0))))
(assert (third_0 zero_0 (succ_0 (succ_0 zero_0))))
(assert (=>	(and (diseqNat_0 zero_0 (succ_0 (succ_0 zero_0)))
			(diseqNat_0 zero_0 (succ_0 zero_0)))
		(third_0 zero_0 zero_0)))
(declare-fun twoThirds_0 (Nat_0 Nat_0) Bool)
(assert (twoThirds_0 (succ_0 zero_0) (succ_0 (succ_0 zero_0))))
(assert (=> (diseqNat_0 (succ_0 zero_0) (succ_0 (succ_0 zero_0)))
	    (twoThirds_0 (succ_0 zero_0) (succ_0 zero_0))))
(assert (twoThirds_0 (succ_0 zero_0) (succ_0 (succ_0 zero_0))))
(assert (forall ((x_52 Nat_0) (x_53 Nat_0) (x_54 Nat_0) (y_5 Nat_0))
	(=>	(and (diseqNat_0 (succ_0 y_5) (succ_0 (succ_0 zero_0)))
			(diseqNat_0 (succ_0 y_5) (succ_0 zero_0))
			(minus_0 x_53 (succ_0 y_5) (succ_0 (succ_0 (succ_0 zero_0))))
			(twoThirds_0 x_54 x_53)
			(plus_0 x_52 (succ_0 (succ_0 zero_0)) x_54))
		(twoThirds_0 x_52 (succ_0 y_5)))))
(assert (twoThirds_0 (succ_0 zero_0) (succ_0 (succ_0 zero_0))))
(assert (=> (diseqNat_0 (succ_0 zero_0) (succ_0 (succ_0 zero_0)))
	    (twoThirds_0 (succ_0 zero_0) (succ_0 zero_0))))
(assert (twoThirds_0 (succ_0 zero_0) (succ_0 (succ_0 zero_0))))
(assert (=>	(and (diseqNat_0 zero_0 (succ_0 (succ_0 zero_0)))
			(diseqNat_0 zero_0 (succ_0 zero_0)))
		(twoThirds_0 zero_0 zero_0)))
(declare-fun leq_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_60 Bool_0) (x_6 Nat_0) (z_4 Nat_0))
	(=> (leq_0 x_60 z_4 x_6)
	    (leq_0 x_60 (succ_0 z_4) (succ_0 x_6)))))
(assert (forall ((z_4 Nat_0))
	(leq_0 false_0 (succ_0 z_4) zero_0)))
(assert (forall ((y_6 Nat_0))
	(leq_0 true_0 zero_0 y_6)))
(declare-fun ordered_0 (Bool_0 list_0) Bool)
(assert (forall ((x_117 Bool_0) (x_65 Bool_0) (x_66 Bool_0) (y_8 Nat_0) (xs_1 list_0) (y_7 Nat_0))
	(=>	(and (leq_0 x_65 y_7 y_8)
			(ordered_0 x_66 (cons_0 y_8 xs_1))
			(and_0 x_117 x_65 x_66))
		(ordered_0 x_117 (cons_0 y_7 (cons_0 y_8 xs_1))))))
(assert (forall ((y_7 Nat_0))
	(ordered_0 true_0 (cons_0 y_7 nil_0))))
(assert (ordered_0 true_0 nil_0))
(declare-fun sort_0 (list_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_8 Nat_0) (y_9 Nat_0))
	(=> (leq_0 true_0 x_8 y_9)
	    (sort_0 (cons_0 x_8 (cons_0 y_9 nil_0)) x_8 y_9))))
(assert (forall ((x_71 Bool_0) (x_8 Nat_0) (y_9 Nat_0))
	(=>	(and (diseqBool_0 x_71 true_0)
			(leq_0 x_71 x_8 y_9))
		(sort_0 (cons_0 y_9 (cons_0 x_8 nil_0)) x_8 y_9))))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_73 Nat_0) (x_74 Nat_0) (y_10 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_74 l_0)
			(plus_0 x_73 (succ_0 zero_0) x_74))
		(length_0 x_73 (cons_0 y_10 l_0)))))
(assert (length_0 zero_0 nil_0))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_77 list_0) (z_7 Nat_0) (xs_2 list_0) (z_6 Nat_0))
	(=> (drop_0 x_77 z_6 xs_2)
	    (drop_0 x_77 (succ_0 z_6) (cons_0 z_7 xs_2)))))
(assert (forall ((z_6 Nat_0))
	(drop_0 nil_0 (succ_0 z_6) nil_0)))
(assert (forall ((x_80 list_0))
	(drop_0 x_80 zero_0 x_80)))
(declare-fun splitAt_0 (pair_0 Nat_0 list_0) Bool)
(assert (forall ((x_82 list_0) (x_83 list_0) (x_11 Nat_0) (y_12 list_0))
	(=>	(and (take_0 x_82 x_11 y_12)
			(drop_0 x_83 x_11 y_12))
		(splitAt_0 (pair_1 x_82 x_83) x_11 y_12))))
(declare-fun x_12 (list_0 list_0 list_0) Bool)
(assert (forall ((x_85 list_0) (z_8 Nat_0) (xs_3 list_0) (y_13 list_0))
	(=> (x_12 x_85 xs_3 y_13)
	    (x_12 (cons_0 z_8 x_85) (cons_0 z_8 xs_3) y_13))))
(assert (forall ((x_86 list_0))
	(x_12 x_86 nil_0 x_86)))
(declare-fun nstoogesort_0 (list_0 list_0) Bool)
(declare-fun nstoogesort_1 (list_0 list_0) Bool)
(declare-fun nstoogesort_2 (list_0 list_0) Bool)
(assert (forall ((x_90 list_0) (x_91 list_0) (x_87 Nat_0) (x_88 Nat_0) (ys_0 list_0) (zs_0 list_0) (x_17 list_0))
	(=>	(and (nstoogesort_1 x_91 ys_0)
			(x_12 x_90 x_91 zs_0)
			(length_0 x_87 x_17)
			(twoThirds_0 x_88 x_87)
			(splitAt_0 (pair_1 ys_0 zs_0) x_88 x_17))
		(nstoogesort_0 x_90 x_17))))
(assert (forall ((x_93 list_0) (x_94 list_0) (x_95 list_0) (x_20 Nat_0) (x_21 list_0) (y_15 Nat_0) (y_14 Nat_0))
	(=>	(and (nstoogesort_0 x_94 (cons_0 y_14 (cons_0 y_15 (cons_0 x_20 x_21))))
			(nstoogesort_2 x_95 x_94)
			(nstoogesort_0 x_93 x_95))
		(nstoogesort_1 x_93 (cons_0 y_14 (cons_0 y_15 (cons_0 x_20 x_21)))))))
(assert (forall ((x_97 list_0) (y_15 Nat_0) (y_14 Nat_0))
	(=> (sort_0 x_97 y_14 y_15)
	    (nstoogesort_1 x_97 (cons_0 y_14 (cons_0 y_15 nil_0))))))
(assert (forall ((y_14 Nat_0))
	(nstoogesort_1 (cons_0 y_14 nil_0) (cons_0 y_14 nil_0))))
(assert (nstoogesort_1 nil_0 nil_0))
(assert (forall ((x_104 list_0) (x_105 list_0) (x_101 Nat_0) (x_102 Nat_0) (ys_1 list_0) (zs_1 list_0) (x_22 list_0))
	(=>	(and (nstoogesort_1 x_105 zs_1)
			(x_12 x_104 ys_1 x_105)
			(length_0 x_101 x_22)
			(third_0 x_102 x_101)
			(splitAt_0 (pair_1 ys_1 zs_1) x_102 x_22))
		(nstoogesort_2 x_104 x_22))))
(assert (forall ((x_107 Nat_0) (x_108 Nat_0) (x_109 Nat_0) (x_110 Nat_0) (x_23 Nat_0) (y_16 Nat_0) (z_10 Nat_0))
	(=>	(and (diseqNat_0 x_108 x_110)
			(plus_0 x_107 y_16 z_10)
			(plus_0 x_108 x_23 x_107)
			(plus_0 x_109 x_23 y_16)
			(plus_0 x_110 x_109 z_10))
		false)))
(assert (forall ((x_111 Nat_0) (x_112 Nat_0) (x_24 Nat_0) (y_17 Nat_0))
	(=>	(and (diseqNat_0 x_111 x_112)
			(plus_0 x_111 x_24 y_17)
			(plus_0 x_112 y_17 x_24))
		false)))
(assert (forall ((x_113 Nat_0) (x_25 Nat_0))
	(=>	(and (diseqNat_0 x_113 x_25)
			(plus_0 x_113 x_25 zero_0))
		false)))
(assert (forall ((x_114 Nat_0) (x_26 Nat_0))
	(=>	(and (diseqNat_0 x_114 x_26)
			(plus_0 x_114 zero_0 x_26))
		false)))
(assert (forall ((x_115 list_0) (x_116 Bool_0) (xs_4 list_0))
	(=>	(and (diseqBool_0 x_116 true_0)
			(nstoogesort_1 x_115 xs_4)
			(ordered_0 x_116 x_115))
		false)))
(check-sat)