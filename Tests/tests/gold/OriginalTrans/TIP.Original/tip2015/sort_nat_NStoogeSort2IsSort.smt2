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
(assert (forall ((x_127 Nat_0))
	(p_1 x_127 (succ_0 x_127))))
(assert (iszero_0 zero_0))
(assert (forall ((x_129 Nat_0))
	(issucc_0 (succ_0 x_129))))
(assert (forall ((x_130 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_130))))
(assert (forall ((x_131 Nat_0))
	(diseqNat_0 (succ_0 x_131) zero_0)))
(assert (forall ((x_132 Nat_0) (x_133 Nat_0))
	(=> (diseqNat_0 x_132 x_133)
	    (diseqNat_0 (succ_0 x_132) (succ_0 x_133)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_135 Nat_0) (x_136 list_0))
	(head_1 x_135 (cons_0 x_135 x_136))))
(assert (forall ((x_135 Nat_0) (x_136 list_0))
	(tail_1 x_136 (cons_0 x_135 x_136))))
(assert (isnil_0 nil_0))
(assert (forall ((x_138 Nat_0) (x_139 list_0))
	(iscons_0 (cons_0 x_138 x_139))))
(assert (forall ((x_140 Nat_0) (x_141 list_0))
	(diseqlist_0 nil_0 (cons_0 x_140 x_141))))
(assert (forall ((x_142 Nat_0) (x_143 list_0))
	(diseqlist_0 (cons_0 x_142 x_143) nil_0)))
(assert (forall ((x_144 Nat_0) (x_145 list_0) (x_146 Nat_0) (x_147 list_0))
	(=> (diseqNat_0 x_144 x_146)
	    (diseqlist_0 (cons_0 x_144 x_145) (cons_0 x_146 x_147)))))
(assert (forall ((x_144 Nat_0) (x_145 list_0) (x_146 Nat_0) (x_147 list_0))
	(=> (diseqlist_0 x_145 x_147)
	    (diseqlist_0 (cons_0 x_144 x_145) (cons_0 x_146 x_147)))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 list_0) (projpair_1 list_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (list_0 pair_0) Bool)
(declare-fun projpair_3 (list_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_148 list_0) (x_149 list_0))
	(projpair_2 x_148 (pair_1 x_148 x_149))))
(assert (forall ((x_148 list_0) (x_149 list_0))
	(projpair_3 x_149 (pair_1 x_148 x_149))))
(assert (forall ((x_151 list_0) (x_152 list_0))
	(ispair_0 (pair_1 x_151 x_152))))
(assert (forall ((x_153 list_0) (x_154 list_0) (x_155 list_0) (x_156 list_0))
	(=> (diseqlist_0 x_153 x_155)
	    (diseqpair_0 (pair_1 x_153 x_154) (pair_1 x_155 x_156)))))
(assert (forall ((x_153 list_0) (x_154 list_0) (x_155 list_0) (x_156 list_0))
	(=> (diseqlist_0 x_154 x_156)
	    (diseqpair_0 (pair_1 x_153 x_154) (pair_1 x_155 x_156)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_29 list_0) (z_1 Nat_0) (xs_0 list_0) (z_0 Nat_0))
	(=> (take_0 x_29 z_0 xs_0)
	    (take_0 (cons_0 z_1 x_29) (succ_0 z_0) (cons_0 z_1 xs_0)))))
(assert (forall ((z_0 Nat_0))
	(take_0 nil_0 (succ_0 z_0) nil_0)))
(assert (forall ((y_0 list_0))
	(take_0 nil_0 zero_0 y_0)))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_33 Nat_0) (z_2 Nat_0) (y_1 Nat_0))
	(=> (plus_0 x_33 z_2 y_1)
	    (plus_0 (succ_0 x_33) (succ_0 z_2) y_1))))
(assert (forall ((x_34 Nat_0))
	(plus_0 x_34 zero_0 x_34)))
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_35 Nat_0) (y_3 Nat_0) (z_3 Nat_0))
	(=> (minus_0 x_35 z_3 y_3)
	    (minus_0 x_35 (succ_0 z_3) (succ_0 y_3)))))
(assert (forall ((z_3 Nat_0))
	(minus_0 zero_0 (succ_0 z_3) zero_0)))
(assert (forall ((y_2 Nat_0))
	(minus_0 zero_0 zero_0 y_2)))
(declare-fun third_0 (Nat_0 Nat_0) Bool)
(assert (third_0 zero_0 (succ_0 (succ_0 zero_0))))
(assert (=> (diseqNat_0 (succ_0 zero_0) (succ_0 (succ_0 zero_0)))
	    (third_0 zero_0 (succ_0 zero_0))))
(assert (third_0 zero_0 (succ_0 (succ_0 zero_0))))
(assert (forall ((x_42 Nat_0) (x_43 Nat_0) (x_44 Nat_0) (y_4 Nat_0))
	(=>	(and (diseqNat_0 (succ_0 y_4) (succ_0 (succ_0 zero_0)))
			(diseqNat_0 (succ_0 y_4) (succ_0 zero_0))
			(minus_0 x_43 (succ_0 y_4) (succ_0 (succ_0 (succ_0 zero_0))))
			(third_0 x_44 x_43)
			(plus_0 x_42 (succ_0 zero_0) x_44))
		(third_0 x_42 (succ_0 y_4)))))
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
(assert (forall ((x_53 Nat_0) (x_54 Nat_0) (x_55 Nat_0) (y_5 Nat_0))
	(=>	(and (diseqNat_0 (succ_0 y_5) (succ_0 (succ_0 zero_0)))
			(diseqNat_0 (succ_0 y_5) (succ_0 zero_0))
			(minus_0 x_54 (succ_0 y_5) (succ_0 (succ_0 (succ_0 zero_0))))
			(twoThirds_0 x_55 x_54)
			(plus_0 x_53 (succ_0 (succ_0 zero_0)) x_55))
		(twoThirds_0 x_53 (succ_0 y_5)))))
(assert (twoThirds_0 (succ_0 zero_0) (succ_0 (succ_0 zero_0))))
(assert (=> (diseqNat_0 (succ_0 zero_0) (succ_0 (succ_0 zero_0)))
	    (twoThirds_0 (succ_0 zero_0) (succ_0 zero_0))))
(assert (twoThirds_0 (succ_0 zero_0) (succ_0 (succ_0 zero_0))))
(assert (=>	(and (diseqNat_0 zero_0 (succ_0 (succ_0 zero_0)))
			(diseqNat_0 zero_0 (succ_0 zero_0)))
		(twoThirds_0 zero_0 zero_0)))
(declare-fun leq_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_61 Bool_0) (x_6 Nat_0) (z_4 Nat_0))
	(=> (leq_0 x_61 z_4 x_6)
	    (leq_0 x_61 (succ_0 z_4) (succ_0 x_6)))))
(assert (forall ((z_4 Nat_0))
	(leq_0 false_0 (succ_0 z_4) zero_0)))
(assert (forall ((y_6 Nat_0))
	(leq_0 true_0 zero_0 y_6)))
(declare-fun sort_0 (list_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_7 Nat_0) (y_7 Nat_0))
	(=> (leq_0 true_0 x_7 y_7)
	    (sort_0 (cons_0 x_7 (cons_0 y_7 nil_0)) x_7 y_7))))
(assert (forall ((x_67 Bool_0) (x_7 Nat_0) (y_7 Nat_0))
	(=>	(and (diseqBool_0 x_67 true_0)
			(leq_0 x_67 x_7 y_7))
		(sort_0 (cons_0 y_7 (cons_0 x_7 nil_0)) x_7 y_7))))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_69 Nat_0) (x_70 Nat_0) (y_8 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_70 l_0)
			(plus_0 x_69 (succ_0 zero_0) x_70))
		(length_0 x_69 (cons_0 y_8 l_0)))))
(assert (length_0 zero_0 nil_0))
(declare-fun insert_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((z_5 Nat_0) (xs_1 list_0) (x_9 Nat_0))
	(=> (leq_0 true_0 x_9 z_5)
	    (insert_0 (cons_0 x_9 (cons_0 z_5 xs_1)) x_9 (cons_0 z_5 xs_1)))))
(assert (forall ((x_77 list_0) (x_75 Bool_0) (z_5 Nat_0) (xs_1 list_0) (x_9 Nat_0))
	(=>	(and (diseqBool_0 x_75 true_0)
			(insert_0 x_77 x_9 xs_1)
			(leq_0 x_75 x_9 z_5))
		(insert_0 (cons_0 z_5 x_77) x_9 (cons_0 z_5 xs_1)))))
(assert (forall ((x_9 Nat_0))
	(insert_0 (cons_0 x_9 nil_0) x_9 nil_0)))
(declare-fun isort_0 (list_0 list_0) Bool)
(assert (forall ((x_79 list_0) (x_80 list_0) (y_10 Nat_0) (xs_2 list_0))
	(=>	(and (isort_0 x_80 xs_2)
			(insert_0 x_79 y_10 x_80))
		(isort_0 x_79 (cons_0 y_10 xs_2)))))
(assert (isort_0 nil_0 nil_0))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_83 list_0) (z_7 Nat_0) (xs_3 list_0) (z_6 Nat_0))
	(=> (drop_0 x_83 z_6 xs_3)
	    (drop_0 x_83 (succ_0 z_6) (cons_0 z_7 xs_3)))))
(assert (forall ((z_6 Nat_0))
	(drop_0 nil_0 (succ_0 z_6) nil_0)))
(assert (forall ((x_86 list_0))
	(drop_0 x_86 zero_0 x_86)))
(declare-fun splitAt_0 (pair_0 Nat_0 list_0) Bool)
(assert (forall ((x_88 list_0) (x_89 list_0) (x_12 Nat_0) (y_12 list_0))
	(=>	(and (take_0 x_88 x_12 y_12)
			(drop_0 x_89 x_12 y_12))
		(splitAt_0 (pair_1 x_88 x_89) x_12 y_12))))
(declare-fun x_13 (list_0 list_0 list_0) Bool)
(assert (forall ((x_91 list_0) (z_8 Nat_0) (xs_4 list_0) (y_13 list_0))
	(=> (x_13 x_91 xs_4 y_13)
	    (x_13 (cons_0 z_8 x_91) (cons_0 z_8 xs_4) y_13))))
(assert (forall ((x_92 list_0))
	(x_13 x_92 nil_0 x_92)))
(declare-fun nstoogesort_0 (list_0 list_0) Bool)
(declare-fun nstoogesort_1 (list_0 list_0) Bool)
(declare-fun nstoogesort_2 (list_0 list_0) Bool)
(assert (forall ((x_96 list_0) (x_97 list_0) (x_93 Nat_0) (x_94 Nat_0) (ys_0 list_0) (zs_0 list_0) (x_18 list_0))
	(=>	(and (nstoogesort_1 x_97 ys_0)
			(x_13 x_96 x_97 zs_0)
			(length_0 x_93 x_18)
			(twoThirds_0 x_94 x_93)
			(splitAt_0 (pair_1 ys_0 zs_0) x_94 x_18))
		(nstoogesort_0 x_96 x_18))))
(assert (forall ((x_100 list_0) (x_101 list_0) (x_102 list_0) (x_21 Nat_0) (x_22 list_0) (y_15 Nat_0) (y_14 Nat_0))
	(=>	(and (nstoogesort_0 x_100 (cons_0 y_14 (cons_0 y_15 (cons_0 x_21 x_22))))
			(nstoogesort_2 x_101 x_100)
			(nstoogesort_0 x_102 x_101))
		(nstoogesort_1 x_102 (cons_0 y_14 (cons_0 y_15 (cons_0 x_21 x_22)))))))
(assert (forall ((x_103 list_0) (y_15 Nat_0) (y_14 Nat_0))
	(=> (sort_0 x_103 y_14 y_15)
	    (nstoogesort_1 x_103 (cons_0 y_14 (cons_0 y_15 nil_0))))))
(assert (forall ((y_14 Nat_0))
	(nstoogesort_1 (cons_0 y_14 nil_0) (cons_0 y_14 nil_0))))
(assert (nstoogesort_1 nil_0 nil_0))
(assert (forall ((x_110 list_0) (x_111 list_0) (x_107 Nat_0) (x_108 Nat_0) (ys_1 list_0) (zs_1 list_0) (x_23 list_0))
	(=>	(and (nstoogesort_1 x_111 zs_1)
			(x_13 x_110 ys_1 x_111)
			(length_0 x_107 x_23)
			(third_0 x_108 x_107)
			(splitAt_0 (pair_1 ys_1 zs_1) x_108 x_23))
		(nstoogesort_2 x_110 x_23))))
(assert (forall ((x_113 Nat_0) (x_114 Nat_0) (x_115 Nat_0) (x_116 Nat_0) (x_24 Nat_0) (y_16 Nat_0) (z_10 Nat_0))
	(=>	(and (diseqNat_0 x_114 x_116)
			(plus_0 x_113 y_16 z_10)
			(plus_0 x_114 x_24 x_113)
			(plus_0 x_115 x_24 y_16)
			(plus_0 x_116 x_115 z_10))
		false)))
(assert (forall ((x_117 Nat_0) (x_118 Nat_0) (x_25 Nat_0) (y_17 Nat_0))
	(=>	(and (diseqNat_0 x_117 x_118)
			(plus_0 x_117 x_25 y_17)
			(plus_0 x_118 y_17 x_25))
		false)))
(assert (forall ((x_119 Nat_0) (x_26 Nat_0))
	(=>	(and (diseqNat_0 x_119 x_26)
			(plus_0 x_119 x_26 zero_0))
		false)))
(assert (forall ((x_120 Nat_0) (x_27 Nat_0))
	(=>	(and (diseqNat_0 x_120 x_27)
			(plus_0 x_120 zero_0 x_27))
		false)))
(assert (forall ((x_121 list_0) (x_122 list_0) (xs_5 list_0))
	(=>	(and (diseqlist_0 x_121 x_122)
			(nstoogesort_1 x_121 xs_5)
			(isort_0 x_122 xs_5))
		false)))
(check-sat)
