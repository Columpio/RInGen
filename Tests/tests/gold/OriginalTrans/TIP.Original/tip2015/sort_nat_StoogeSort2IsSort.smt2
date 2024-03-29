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
(assert (forall ((x_149 Nat_0))
	(p_1 x_149 (succ_0 x_149))))
(assert (iszero_0 zero_0))
(assert (forall ((x_151 Nat_0))
	(issucc_0 (succ_0 x_151))))
(assert (forall ((x_152 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_152))))
(assert (forall ((x_153 Nat_0))
	(diseqNat_0 (succ_0 x_153) zero_0)))
(assert (forall ((x_154 Nat_0) (x_155 Nat_0))
	(=> (diseqNat_0 x_154 x_155)
	    (diseqNat_0 (succ_0 x_154) (succ_0 x_155)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_157 Nat_0) (x_158 list_0))
	(head_1 x_157 (cons_0 x_157 x_158))))
(assert (forall ((x_157 Nat_0) (x_158 list_0))
	(tail_1 x_158 (cons_0 x_157 x_158))))
(assert (isnil_0 nil_0))
(assert (forall ((x_160 Nat_0) (x_161 list_0))
	(iscons_0 (cons_0 x_160 x_161))))
(assert (forall ((x_162 Nat_0) (x_163 list_0))
	(diseqlist_0 nil_0 (cons_0 x_162 x_163))))
(assert (forall ((x_164 Nat_0) (x_165 list_0))
	(diseqlist_0 (cons_0 x_164 x_165) nil_0)))
(assert (forall ((x_166 Nat_0) (x_167 list_0) (x_168 Nat_0) (x_169 list_0))
	(=> (diseqNat_0 x_166 x_168)
	    (diseqlist_0 (cons_0 x_166 x_167) (cons_0 x_168 x_169)))))
(assert (forall ((x_166 Nat_0) (x_167 list_0) (x_168 Nat_0) (x_169 list_0))
	(=> (diseqlist_0 x_167 x_169)
	    (diseqlist_0 (cons_0 x_166 x_167) (cons_0 x_168 x_169)))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 list_0) (projpair_1 list_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (list_0 pair_0) Bool)
(declare-fun projpair_3 (list_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_170 list_0) (x_171 list_0))
	(projpair_2 x_170 (pair_1 x_170 x_171))))
(assert (forall ((x_170 list_0) (x_171 list_0))
	(projpair_3 x_171 (pair_1 x_170 x_171))))
(assert (forall ((x_173 list_0) (x_174 list_0))
	(ispair_0 (pair_1 x_173 x_174))))
(assert (forall ((x_175 list_0) (x_176 list_0) (x_177 list_0) (x_178 list_0))
	(=> (diseqlist_0 x_175 x_177)
	    (diseqpair_0 (pair_1 x_175 x_176) (pair_1 x_177 x_178)))))
(assert (forall ((x_175 list_0) (x_176 list_0) (x_177 list_0) (x_178 list_0))
	(=> (diseqlist_0 x_176 x_178)
	    (diseqpair_0 (pair_1 x_175 x_176) (pair_1 x_177 x_178)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_38 list_0) (z_1 Nat_0) (xs_0 list_0) (z_0 Nat_0))
	(=> (take_0 x_38 z_0 xs_0)
	    (take_0 (cons_0 z_1 x_38) (succ_0 z_0) (cons_0 z_1 xs_0)))))
(assert (forall ((z_0 Nat_0))
	(take_0 nil_0 (succ_0 z_0) nil_0)))
(assert (forall ((y_0 list_0))
	(take_0 nil_0 zero_0 y_0)))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_42 Nat_0) (z_2 Nat_0) (y_1 Nat_0))
	(=> (plus_0 x_42 z_2 y_1)
	    (plus_0 (succ_0 x_42) (succ_0 z_2) y_1))))
(assert (forall ((x_43 Nat_0))
	(plus_0 x_43 zero_0 x_43)))
(declare-fun times_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_44 Nat_0) (x_45 Nat_0) (z_3 Nat_0) (y_2 Nat_0))
	(=>	(and (times_0 x_45 z_3 y_2)
			(plus_0 x_44 y_2 x_45))
		(times_0 x_44 (succ_0 z_3) y_2))))
(assert (forall ((y_2 Nat_0))
	(times_0 zero_0 zero_0 y_2)))
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_48 Nat_0) (y_4 Nat_0) (z_4 Nat_0))
	(=> (minus_0 x_48 z_4 y_4)
	    (minus_0 x_48 (succ_0 z_4) (succ_0 y_4)))))
(assert (forall ((z_4 Nat_0))
	(minus_0 zero_0 (succ_0 z_4) zero_0)))
(assert (forall ((y_3 Nat_0))
	(minus_0 zero_0 zero_0 y_3)))
(declare-fun lt_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_52 Bool_0) (n_0 Nat_0) (z_5 Nat_0))
	(=> (lt_0 x_52 n_0 z_5)
	    (lt_0 x_52 (succ_0 n_0) (succ_0 z_5)))))
(assert (forall ((z_5 Nat_0))
	(lt_0 true_0 zero_0 (succ_0 z_5))))
(assert (forall ((x_4 Nat_0))
	(lt_0 false_0 x_4 zero_0)))
(declare-fun leq_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_56 Bool_0) (x_6 Nat_0) (z_6 Nat_0))
	(=> (leq_0 x_56 z_6 x_6)
	    (leq_0 x_56 (succ_0 z_6) (succ_0 x_6)))))
(assert (forall ((z_6 Nat_0))
	(leq_0 false_0 (succ_0 z_6) zero_0)))
(assert (forall ((y_6 Nat_0))
	(leq_0 true_0 zero_0 y_6)))
(declare-fun sort_0 (list_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_7 Nat_0) (y_7 Nat_0))
	(=> (leq_0 true_0 x_7 y_7)
	    (sort_0 (cons_0 x_7 (cons_0 y_7 nil_0)) x_7 y_7))))
(assert (forall ((x_62 Bool_0) (x_7 Nat_0) (y_7 Nat_0))
	(=>	(and (diseqBool_0 x_62 true_0)
			(leq_0 x_62 x_7 y_7))
		(sort_0 (cons_0 y_7 (cons_0 x_7 nil_0)) x_7 y_7))))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_64 Nat_0) (x_65 Nat_0) (y_8 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_65 l_0)
			(plus_0 x_64 (succ_0 zero_0) x_65))
		(length_0 x_64 (cons_0 y_8 l_0)))))
(assert (length_0 zero_0 nil_0))
(declare-fun insert_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((z_7 Nat_0) (xs_1 list_0) (x_9 Nat_0))
	(=> (leq_0 true_0 x_9 z_7)
	    (insert_0 (cons_0 x_9 (cons_0 z_7 xs_1)) x_9 (cons_0 z_7 xs_1)))))
(assert (forall ((x_72 list_0) (x_70 Bool_0) (z_7 Nat_0) (xs_1 list_0) (x_9 Nat_0))
	(=>	(and (diseqBool_0 x_70 true_0)
			(insert_0 x_72 x_9 xs_1)
			(leq_0 x_70 x_9 z_7))
		(insert_0 (cons_0 z_7 x_72) x_9 (cons_0 z_7 xs_1)))))
(assert (forall ((x_9 Nat_0))
	(insert_0 (cons_0 x_9 nil_0) x_9 nil_0)))
(declare-fun isort_0 (list_0 list_0) Bool)
(assert (forall ((x_74 list_0) (x_75 list_0) (y_10 Nat_0) (xs_2 list_0))
	(=>	(and (isort_0 x_75 xs_2)
			(insert_0 x_74 y_10 x_75))
		(isort_0 x_74 (cons_0 y_10 xs_2)))))
(assert (isort_0 nil_0 nil_0))
(declare-fun idiv_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_11 Nat_0) (y_11 Nat_0))
	(=> (lt_0 true_0 x_11 y_11)
	    (idiv_0 zero_0 x_11 y_11))))
(assert (forall ((x_82 Nat_0) (x_83 Nat_0) (x_80 Bool_0) (x_11 Nat_0) (y_11 Nat_0))
	(=>	(and (diseqBool_0 x_80 true_0)
			(minus_0 x_82 x_11 y_11)
			(idiv_0 x_83 x_82 y_11)
			(lt_0 x_80 x_11 y_11))
		(idiv_0 (succ_0 x_83) x_11 y_11))))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_84 list_0) (z_9 Nat_0) (xs_3 list_0) (z_8 Nat_0))
	(=> (drop_0 x_84 z_8 xs_3)
	    (drop_0 x_84 (succ_0 z_8) (cons_0 z_9 xs_3)))))
(assert (forall ((z_8 Nat_0))
	(drop_0 nil_0 (succ_0 z_8) nil_0)))
(assert (forall ((x_87 list_0))
	(drop_0 x_87 zero_0 x_87)))
(declare-fun splitAt_0 (pair_0 Nat_0 list_0) Bool)
(assert (forall ((x_89 list_0) (x_90 list_0) (x_13 Nat_0) (y_13 list_0))
	(=>	(and (take_0 x_89 x_13 y_13)
			(drop_0 x_90 x_13 y_13))
		(splitAt_0 (pair_1 x_89 x_90) x_13 y_13))))
(declare-fun x_14 (list_0 list_0 list_0) Bool)
(assert (forall ((x_92 list_0) (z_10 Nat_0) (xs_4 list_0) (y_14 list_0))
	(=> (x_14 x_92 xs_4 y_14)
	    (x_14 (cons_0 z_10 x_92) (cons_0 z_10 xs_4) y_14))))
(assert (forall ((x_93 list_0))
	(x_14 x_93 nil_0 x_93)))
(declare-fun stoogesort_0 (list_0 list_0) Bool)
(declare-fun stoogesort_1 (list_0 list_0) Bool)
(declare-fun stoogesort_2 (list_0 list_0) Bool)
(assert (forall ((x_99 list_0) (x_100 list_0) (x_94 Nat_0) (x_95 Nat_0) (x_96 Nat_0) (ys_0 list_0) (zs_0 list_0) (x_19 list_0))
	(=>	(and (stoogesort_1 x_99 ys_0)
			(x_14 x_100 x_99 zs_0)
			(length_0 x_94 x_19)
			(times_0 x_95 (succ_0 (succ_0 zero_0)) x_94)
			(idiv_0 x_96 (succ_0 x_95) (succ_0 (succ_0 (succ_0 zero_0))))
			(splitAt_0 (pair_1 ys_0 zs_0) x_96 x_19))
		(stoogesort_0 x_100 x_19))))
(assert (forall ((x_101 list_0) (x_102 list_0) (x_103 list_0) (x_22 Nat_0) (x_23 list_0) (y_16 Nat_0) (y_15 Nat_0))
	(=>	(and (stoogesort_0 x_102 (cons_0 y_15 (cons_0 y_16 (cons_0 x_22 x_23))))
			(stoogesort_2 x_103 x_102)
			(stoogesort_0 x_101 x_103))
		(stoogesort_1 x_101 (cons_0 y_15 (cons_0 y_16 (cons_0 x_22 x_23)))))))
(assert (forall ((x_105 list_0) (y_16 Nat_0) (y_15 Nat_0))
	(=> (sort_0 x_105 y_15 y_16)
	    (stoogesort_1 x_105 (cons_0 y_15 (cons_0 y_16 nil_0))))))
(assert (forall ((y_15 Nat_0))
	(stoogesort_1 (cons_0 y_15 nil_0) (cons_0 y_15 nil_0))))
(assert (stoogesort_1 nil_0 nil_0))
(assert (forall ((x_112 list_0) (x_113 list_0) (x_109 Nat_0) (x_110 Nat_0) (ys_1 list_0) (zs_1 list_0) (x_24 list_0))
	(=>	(and (stoogesort_1 x_113 zs_1)
			(x_14 x_112 ys_1 x_113)
			(length_0 x_109 x_24)
			(idiv_0 x_110 x_109 (succ_0 (succ_0 (succ_0 zero_0))))
			(splitAt_0 (pair_1 ys_1 zs_1) x_110 x_24))
		(stoogesort_2 x_112 x_24))))
(assert (forall ((x_115 Nat_0) (x_116 Nat_0) (x_117 Nat_0) (x_118 Nat_0) (x_25 Nat_0) (y_17 Nat_0) (z_12 Nat_0))
	(=>	(and (diseqNat_0 x_116 x_118)
			(times_0 x_115 y_17 z_12)
			(times_0 x_116 x_25 x_115)
			(times_0 x_117 x_25 y_17)
			(times_0 x_118 x_117 z_12))
		false)))
(assert (forall ((x_119 Nat_0) (x_120 Nat_0) (x_121 Nat_0) (x_122 Nat_0) (x_26 Nat_0) (y_18 Nat_0) (z_13 Nat_0))
	(=>	(and (diseqNat_0 x_120 x_122)
			(plus_0 x_119 y_18 z_13)
			(plus_0 x_120 x_26 x_119)
			(plus_0 x_121 x_26 y_18)
			(plus_0 x_122 x_121 z_13))
		false)))
(assert (forall ((x_123 Nat_0) (x_124 Nat_0) (x_27 Nat_0) (y_19 Nat_0))
	(=>	(and (diseqNat_0 x_123 x_124)
			(times_0 x_123 x_27 y_19)
			(times_0 x_124 y_19 x_27))
		false)))
(assert (forall ((x_125 Nat_0) (x_126 Nat_0) (x_28 Nat_0) (y_20 Nat_0))
	(=>	(and (diseqNat_0 x_125 x_126)
			(plus_0 x_125 x_28 y_20)
			(plus_0 x_126 y_20 x_28))
		false)))
(assert (forall ((x_127 Nat_0) (x_128 Nat_0) (x_129 Nat_0) (x_130 Nat_0) (x_131 Nat_0) (x_29 Nat_0) (y_21 Nat_0) (z_14 Nat_0))
	(=>	(and (diseqNat_0 x_128 x_131)
			(plus_0 x_127 y_21 z_14)
			(times_0 x_128 x_29 x_127)
			(times_0 x_129 x_29 y_21)
			(times_0 x_130 x_29 z_14)
			(plus_0 x_131 x_129 x_130))
		false)))
(assert (forall ((x_132 Nat_0) (x_133 Nat_0) (x_134 Nat_0) (x_135 Nat_0) (x_136 Nat_0) (x_30 Nat_0) (y_22 Nat_0) (z_15 Nat_0))
	(=>	(and (diseqNat_0 x_133 x_136)
			(plus_0 x_132 x_30 y_22)
			(times_0 x_133 x_132 z_15)
			(times_0 x_134 x_30 z_15)
			(times_0 x_135 y_22 z_15)
			(plus_0 x_136 x_134 x_135))
		false)))
(assert (forall ((x_137 Nat_0) (x_31 Nat_0))
	(=>	(and (diseqNat_0 x_137 x_31)
			(times_0 x_137 x_31 (succ_0 zero_0)))
		false)))
(assert (forall ((x_138 Nat_0) (x_32 Nat_0))
	(=>	(and (diseqNat_0 x_138 x_32)
			(times_0 x_138 (succ_0 zero_0) x_32))
		false)))
(assert (forall ((x_139 Nat_0) (x_33 Nat_0))
	(=>	(and (diseqNat_0 x_139 x_33)
			(plus_0 x_139 x_33 zero_0))
		false)))
(assert (forall ((x_140 Nat_0) (x_34 Nat_0))
	(=>	(and (diseqNat_0 x_140 x_34)
			(plus_0 x_140 zero_0 x_34))
		false)))
(assert (forall ((x_141 Nat_0) (x_35 Nat_0))
	(=>	(and (diseqNat_0 x_141 zero_0)
			(times_0 x_141 x_35 zero_0))
		false)))
(assert (forall ((x_142 Nat_0) (x_36 Nat_0))
	(=>	(and (diseqNat_0 x_142 zero_0)
			(times_0 x_142 zero_0 x_36))
		false)))
(assert (forall ((x_143 list_0) (x_144 list_0) (xs_5 list_0))
	(=>	(and (diseqlist_0 x_143 x_144)
			(stoogesort_1 x_143 xs_5)
			(isort_0 x_144 xs_5))
		false)))
(check-sat)
