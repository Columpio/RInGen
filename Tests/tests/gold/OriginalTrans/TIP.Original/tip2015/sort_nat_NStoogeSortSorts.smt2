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
(assert (forall ((x_117 Nat_0))
	(p_1 x_117 (succ_0 x_117))))
(assert (iszero_0 zero_0))
(assert (forall ((x_119 Nat_0))
	(issucc_0 (succ_0 x_119))))
(assert (forall ((x_120 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_120))))
(assert (forall ((x_121 Nat_0))
	(diseqNat_0 (succ_0 x_121) zero_0)))
(assert (forall ((x_122 Nat_0) (x_123 Nat_0))
	(=> (diseqNat_0 x_122 x_123)
	    (diseqNat_0 (succ_0 x_122) (succ_0 x_123)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_125 Nat_0) (x_126 list_0))
	(head_1 x_125 (cons_0 x_125 x_126))))
(assert (forall ((x_125 Nat_0) (x_126 list_0))
	(tail_1 x_126 (cons_0 x_125 x_126))))
(assert (isnil_0 nil_0))
(assert (forall ((x_128 Nat_0) (x_129 list_0))
	(iscons_0 (cons_0 x_128 x_129))))
(assert (forall ((x_130 Nat_0) (x_131 list_0))
	(diseqlist_0 nil_0 (cons_0 x_130 x_131))))
(assert (forall ((x_132 Nat_0) (x_133 list_0))
	(diseqlist_0 (cons_0 x_132 x_133) nil_0)))
(assert (forall ((x_134 Nat_0) (x_135 list_0) (x_136 Nat_0) (x_137 list_0))
	(=> (diseqNat_0 x_134 x_136)
	    (diseqlist_0 (cons_0 x_134 x_135) (cons_0 x_136 x_137)))))
(assert (forall ((x_134 Nat_0) (x_135 list_0) (x_136 Nat_0) (x_137 list_0))
	(=> (diseqlist_0 x_135 x_137)
	    (diseqlist_0 (cons_0 x_134 x_135) (cons_0 x_136 x_137)))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 list_0) (projpair_1 list_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (list_0 pair_0) Bool)
(declare-fun projpair_3 (list_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_138 list_0) (x_139 list_0))
	(projpair_2 x_138 (pair_1 x_138 x_139))))
(assert (forall ((x_138 list_0) (x_139 list_0))
	(projpair_3 x_139 (pair_1 x_138 x_139))))
(assert (forall ((x_141 list_0) (x_142 list_0))
	(ispair_0 (pair_1 x_141 x_142))))
(assert (forall ((x_143 list_0) (x_144 list_0) (x_145 list_0) (x_146 list_0))
	(=> (diseqlist_0 x_143 x_145)
	    (diseqpair_0 (pair_1 x_143 x_144) (pair_1 x_145 x_146)))))
(assert (forall ((x_143 list_0) (x_144 list_0) (x_145 list_0) (x_146 list_0))
	(=> (diseqlist_0 x_144 x_146)
	    (diseqpair_0 (pair_1 x_143 x_144) (pair_1 x_145 x_146)))))
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
(declare-fun leq_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_49 Bool_0) (x_5 Nat_0) (z_4 Nat_0))
	(=> (leq_0 x_49 z_4 x_5)
	    (leq_0 x_49 (succ_0 z_4) (succ_0 x_5)))))
(assert (forall ((z_4 Nat_0))
	(leq_0 false_0 (succ_0 z_4) zero_0)))
(assert (forall ((y_5 Nat_0))
	(leq_0 true_0 zero_0 y_5)))
(declare-fun ordered_0 (Bool_0 list_0) Bool)
(assert (forall ((x_112 Bool_0) (x_54 Bool_0) (x_55 Bool_0) (y_7 Nat_0) (xs_1 list_0) (y_6 Nat_0))
	(=>	(and (leq_0 x_54 y_6 y_7)
			(ordered_0 x_55 (cons_0 y_7 xs_1))
			(and_0 x_112 x_54 x_55))
		(ordered_0 x_112 (cons_0 y_6 (cons_0 y_7 xs_1))))))
(assert (forall ((y_6 Nat_0))
	(ordered_0 true_0 (cons_0 y_6 nil_0))))
(assert (ordered_0 true_0 nil_0))
(declare-fun sort_0 (list_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_7 Nat_0) (y_8 Nat_0))
	(=> (leq_0 true_0 x_7 y_8)
	    (sort_0 (cons_0 x_7 (cons_0 y_8 nil_0)) x_7 y_8))))
(assert (forall ((x_60 Bool_0) (x_7 Nat_0) (y_8 Nat_0))
	(=>	(and (diseqBool_0 x_60 true_0)
			(leq_0 x_60 x_7 y_8))
		(sort_0 (cons_0 y_8 (cons_0 x_7 nil_0)) x_7 y_8))))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_62 Nat_0) (x_63 Nat_0) (y_9 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_63 l_0)
			(plus_0 x_62 (succ_0 zero_0) x_63))
		(length_0 x_62 (cons_0 y_9 l_0)))))
(assert (length_0 zero_0 nil_0))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_66 list_0) (z_7 Nat_0) (xs_2 list_0) (z_6 Nat_0))
	(=> (drop_0 x_66 z_6 xs_2)
	    (drop_0 x_66 (succ_0 z_6) (cons_0 z_7 xs_2)))))
(assert (forall ((z_6 Nat_0))
	(drop_0 nil_0 (succ_0 z_6) nil_0)))
(assert (forall ((x_69 list_0))
	(drop_0 x_69 zero_0 x_69)))
(declare-fun splitAt_0 (pair_0 Nat_0 list_0) Bool)
(assert (forall ((x_71 list_0) (x_72 list_0) (x_10 Nat_0) (y_11 list_0))
	(=>	(and (take_0 x_71 x_10 y_11)
			(drop_0 x_72 x_10 y_11))
		(splitAt_0 (pair_1 x_71 x_72) x_10 y_11))))
(declare-fun x_11 (list_0 list_0 list_0) Bool)
(assert (forall ((x_74 list_0) (z_8 Nat_0) (xs_3 list_0) (y_12 list_0))
	(=> (x_11 x_74 xs_3 y_12)
	    (x_11 (cons_0 z_8 x_74) (cons_0 z_8 xs_3) y_12))))
(assert (forall ((x_75 list_0))
	(x_11 x_75 nil_0 x_75)))
(declare-fun reverse_0 (list_0 list_0) Bool)
(assert (forall ((x_76 list_0) (x_77 list_0) (y_13 Nat_0) (xs_4 list_0))
	(=>	(and (reverse_0 x_77 xs_4)
			(x_11 x_76 x_77 (cons_0 y_13 nil_0)))
		(reverse_0 x_76 (cons_0 y_13 xs_4)))))
(assert (reverse_0 nil_0 nil_0))
(declare-fun nstoogesort_0 (list_0 list_0) Bool)
(declare-fun nstoogesort_1 (list_0 list_0) Bool)
(declare-fun nstoogesort_2 (list_0 list_0) Bool)
(assert (forall ((x_84 list_0) (x_85 list_0) (x_86 list_0) (x_80 Nat_0) (x_81 Nat_0) (x_82 list_0) (ys_0 list_0) (zs_0 list_0) (x_17 list_0))
	(=>	(and (nstoogesort_1 x_85 zs_0)
			(reverse_0 x_86 ys_0)
			(x_11 x_84 x_85 x_86)
			(length_0 x_80 x_17)
			(third_0 x_81 x_80)
			(reverse_0 x_82 x_17)
			(splitAt_0 (pair_1 ys_0 zs_0) x_81 x_82))
		(nstoogesort_0 x_84 x_17))))
(assert (forall ((x_88 list_0) (x_89 list_0) (x_90 list_0) (x_20 Nat_0) (x_21 list_0) (y_15 Nat_0) (y_14 Nat_0))
	(=>	(and (nstoogesort_0 x_89 (cons_0 y_14 (cons_0 y_15 (cons_0 x_20 x_21))))
			(nstoogesort_2 x_90 x_89)
			(nstoogesort_0 x_88 x_90))
		(nstoogesort_1 x_88 (cons_0 y_14 (cons_0 y_15 (cons_0 x_20 x_21)))))))
(assert (forall ((x_92 list_0) (y_15 Nat_0) (y_14 Nat_0))
	(=> (sort_0 x_92 y_14 y_15)
	    (nstoogesort_1 x_92 (cons_0 y_14 (cons_0 y_15 nil_0))))))
(assert (forall ((y_14 Nat_0))
	(nstoogesort_1 (cons_0 y_14 nil_0) (cons_0 y_14 nil_0))))
(assert (nstoogesort_1 nil_0 nil_0))
(assert (forall ((x_100 list_0) (x_101 list_0) (x_96 Nat_0) (x_97 Nat_0) (ys_1 list_0) (zs_1 list_0) (x_22 list_0))
	(=>	(and (nstoogesort_1 x_100 zs_1)
			(x_11 x_101 ys_1 x_100)
			(length_0 x_96 x_22)
			(third_0 x_97 x_96)
			(splitAt_0 (pair_1 ys_1 zs_1) x_97 x_22))
		(nstoogesort_2 x_101 x_22))))
(assert (forall ((x_102 Nat_0) (x_103 Nat_0) (x_104 Nat_0) (x_105 Nat_0) (x_23 Nat_0) (y_16 Nat_0) (z_10 Nat_0))
	(=>	(and (diseqNat_0 x_103 x_105)
			(plus_0 x_102 y_16 z_10)
			(plus_0 x_103 x_23 x_102)
			(plus_0 x_104 x_23 y_16)
			(plus_0 x_105 x_104 z_10))
		false)))
(assert (forall ((x_106 Nat_0) (x_107 Nat_0) (x_24 Nat_0) (y_17 Nat_0))
	(=>	(and (diseqNat_0 x_106 x_107)
			(plus_0 x_106 x_24 y_17)
			(plus_0 x_107 y_17 x_24))
		false)))
(assert (forall ((x_108 Nat_0) (x_25 Nat_0))
	(=>	(and (diseqNat_0 x_108 x_25)
			(plus_0 x_108 x_25 zero_0))
		false)))
(assert (forall ((x_109 Nat_0) (x_26 Nat_0))
	(=>	(and (diseqNat_0 x_109 x_26)
			(plus_0 x_109 zero_0 x_26))
		false)))
(assert (forall ((x_110 list_0) (x_111 Bool_0) (xs_5 list_0))
	(=>	(and (diseqBool_0 x_111 true_0)
			(nstoogesort_1 x_110 xs_5)
			(ordered_0 x_111 x_110))
		false)))
(check-sat)