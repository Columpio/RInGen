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
(assert (forall ((x_81 Nat_0))
	(p_1 x_81 (succ_0 x_81))))
(assert (iszero_0 zero_0))
(assert (forall ((x_83 Nat_0))
	(issucc_0 (succ_0 x_83))))
(assert (forall ((x_84 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_84))))
(assert (forall ((x_85 Nat_0))
	(diseqNat_0 (succ_0 x_85) zero_0)))
(assert (forall ((x_86 Nat_0) (x_87 Nat_0))
	(=> (diseqNat_0 x_86 x_87)
	    (diseqNat_0 (succ_0 x_86) (succ_0 x_87)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_2 (Nat_0 list_0) Bool)
(declare-fun tail_2 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_89 Nat_0) (x_90 list_0))
	(head_2 x_89 (cons_0 x_89 x_90))))
(assert (forall ((x_89 Nat_0) (x_90 list_0))
	(tail_2 x_90 (cons_0 x_89 x_90))))
(assert (isnil_0 nil_0))
(assert (forall ((x_92 Nat_0) (x_93 list_0))
	(iscons_0 (cons_0 x_92 x_93))))
(assert (forall ((x_94 Nat_0) (x_95 list_0))
	(diseqlist_0 nil_0 (cons_0 x_94 x_95))))
(assert (forall ((x_96 Nat_0) (x_97 list_0))
	(diseqlist_0 (cons_0 x_96 x_97) nil_0)))
(assert (forall ((x_100 Nat_0) (x_101 list_0) (x_98 Nat_0) (x_99 list_0))
	(=> (diseqNat_0 x_98 x_100)
	    (diseqlist_0 (cons_0 x_98 x_99) (cons_0 x_100 x_101)))))
(assert (forall ((x_100 Nat_0) (x_101 list_0) (x_98 Nat_0) (x_99 list_0))
	(=> (diseqlist_0 x_99 x_101)
	    (diseqlist_0 (cons_0 x_98 x_99) (cons_0 x_100 x_101)))))
(declare-datatypes ((list_1 0)) (((nil_1 ) (cons_1 (head_1 list_0) (tail_1 list_1)))))
(declare-fun diseqlist_1 (list_1 list_1) Bool)
(declare-fun head_3 (list_0 list_1) Bool)
(declare-fun tail_3 (list_1 list_1) Bool)
(declare-fun isnil_1 (list_1) Bool)
(declare-fun iscons_1 (list_1) Bool)
(assert (forall ((x_103 list_0) (x_104 list_1))
	(head_3 x_103 (cons_1 x_103 x_104))))
(assert (forall ((x_103 list_0) (x_104 list_1))
	(tail_3 x_104 (cons_1 x_103 x_104))))
(assert (isnil_1 nil_1))
(assert (forall ((x_106 list_0) (x_107 list_1))
	(iscons_1 (cons_1 x_106 x_107))))
(assert (forall ((x_108 list_0) (x_109 list_1))
	(diseqlist_1 nil_1 (cons_1 x_108 x_109))))
(assert (forall ((x_110 list_0) (x_111 list_1))
	(diseqlist_1 (cons_1 x_110 x_111) nil_1)))
(assert (forall ((x_112 list_0) (x_113 list_1) (x_114 list_0) (x_115 list_1))
	(=> (diseqlist_0 x_112 x_114)
	    (diseqlist_1 (cons_1 x_112 x_113) (cons_1 x_114 x_115)))))
(assert (forall ((x_112 list_0) (x_113 list_1) (x_114 list_0) (x_115 list_1))
	(=> (diseqlist_1 x_113 x_115)
	    (diseqlist_1 (cons_1 x_112 x_113) (cons_1 x_114 x_115)))))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_19 Nat_0) (z_0 Nat_0) (y_0 Nat_0))
	(=> (plus_0 x_19 z_0 y_0)
	    (plus_0 (succ_0 x_19) (succ_0 z_0) y_0))))
(assert (forall ((x_20 Nat_0))
	(plus_0 x_20 zero_0 x_20)))
(declare-fun leq_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_21 Bool_0) (x_2 Nat_0) (z_1 Nat_0))
	(=> (leq_0 x_21 z_1 x_2)
	    (leq_0 x_21 (succ_0 z_1) (succ_0 x_2)))))
(assert (forall ((z_1 Nat_0))
	(leq_0 false_0 (succ_0 z_1) zero_0)))
(assert (forall ((y_1 Nat_0))
	(leq_0 true_0 zero_0 y_1)))
(declare-fun lmerge_0 (list_0 list_0 list_0) Bool)
(assert (forall ((x_27 list_0) (x_5 Nat_0) (x_6 list_0) (z_2 Nat_0) (x_4 list_0))
	(=>	(and (lmerge_0 x_27 x_4 (cons_0 x_5 x_6))
			(leq_0 true_0 z_2 x_5))
		(lmerge_0 (cons_0 z_2 x_27) (cons_0 z_2 x_4) (cons_0 x_5 x_6)))))
(assert (forall ((x_30 list_0) (x_28 Bool_0) (x_5 Nat_0) (x_6 list_0) (z_2 Nat_0) (x_4 list_0))
	(=>	(and (diseqBool_0 x_28 true_0)
			(lmerge_0 x_30 (cons_0 z_2 x_4) x_6)
			(leq_0 x_28 z_2 x_5))
		(lmerge_0 (cons_0 x_5 x_30) (cons_0 z_2 x_4) (cons_0 x_5 x_6)))))
(assert (forall ((z_2 Nat_0) (x_4 list_0))
	(lmerge_0 (cons_0 z_2 x_4) (cons_0 z_2 x_4) nil_0)))
(assert (forall ((x_32 list_0))
	(lmerge_0 x_32 nil_0 x_32)))
(declare-fun pairwise_0 (list_1 list_1) Bool)
(assert (forall ((x_34 list_0) (x_35 list_1) (ys_0 list_0) (xss_0 list_1) (xs_0 list_0))
	(=>	(and (lmerge_0 x_34 xs_0 ys_0)
			(pairwise_0 x_35 xss_0))
		(pairwise_0 (cons_1 x_34 x_35) (cons_1 xs_0 (cons_1 ys_0 xss_0))))))
(assert (forall ((xs_0 list_0))
	(pairwise_0 (cons_1 xs_0 nil_1) (cons_1 xs_0 nil_1))))
(assert (pairwise_0 nil_1 nil_1))
(declare-fun mergingbu_0 (list_0 list_1) Bool)
(assert (forall ((x_38 list_0) (x_39 list_1) (z_3 list_0) (x_9 list_1) (xs_1 list_0))
	(=>	(and (pairwise_0 x_39 (cons_1 xs_1 (cons_1 z_3 x_9)))
			(mergingbu_0 x_38 x_39))
		(mergingbu_0 x_38 (cons_1 xs_1 (cons_1 z_3 x_9))))))
(assert (forall ((x_41 list_0))
	(mergingbu_0 x_41 (cons_1 x_41 nil_1))))
(assert (mergingbu_0 nil_0 nil_1))
(declare-fun risers_0 (list_1 list_0) Bool)
(assert (forall ((ys_1 list_0) (yss_0 list_1) (y_6 Nat_0) (xs_2 list_0) (y_5 Nat_0))
	(=>	(and (risers_0 (cons_1 ys_1 yss_0) (cons_0 y_6 xs_2))
			(leq_0 true_0 y_5 y_6))
		(risers_0 (cons_1 (cons_0 y_5 ys_1) yss_0) (cons_0 y_5 (cons_0 y_6 xs_2))))))
(assert (forall ((x_48 list_1) (x_46 Bool_0) (y_6 Nat_0) (xs_2 list_0) (y_5 Nat_0))
	(=>	(and (diseqBool_0 x_46 true_0)
			(risers_0 x_48 (cons_0 y_6 xs_2))
			(leq_0 x_46 y_5 y_6))
		(risers_0 (cons_1 (cons_0 y_5 nil_0) x_48) (cons_0 y_5 (cons_0 y_6 xs_2))))))
(assert (forall ((y_6 Nat_0) (xs_2 list_0) (y_5 Nat_0))
	(=>	(and (risers_0 nil_1 (cons_0 y_6 xs_2))
			(leq_0 true_0 y_5 y_6))
		(risers_0 nil_1 (cons_0 y_5 (cons_0 y_6 xs_2))))))
(assert (forall ((x_54 list_1) (x_52 Bool_0) (y_6 Nat_0) (xs_2 list_0) (y_5 Nat_0))
	(=>	(and (diseqBool_0 x_52 true_0)
			(risers_0 x_54 (cons_0 y_6 xs_2))
			(leq_0 x_52 y_5 y_6))
		(risers_0 (cons_1 (cons_0 y_5 nil_0) x_54) (cons_0 y_5 (cons_0 y_6 xs_2))))))
(assert (forall ((y_5 Nat_0))
	(risers_0 (cons_1 (cons_0 y_5 nil_0) nil_1) (cons_0 y_5 nil_0))))
(assert (risers_0 nil_1 nil_0))
(declare-fun msortbu_0 (list_0 list_0) Bool)
(assert (forall ((x_57 list_0) (x_58 list_1) (x_11 list_0))
	(=>	(and (risers_0 x_58 x_11)
			(mergingbu_0 x_57 x_58))
		(msortbu_0 x_57 x_11))))
(declare-fun count_0 (Nat_0 Nat_0 list_0) Bool)
(assert (forall ((x_60 Nat_0) (x_61 Nat_0) (ys_2 list_0) (x_12 Nat_0))
	(=>	(and (count_0 x_61 x_12 ys_2)
			(plus_0 x_60 (succ_0 zero_0) x_61))
		(count_0 x_60 x_12 (cons_0 x_12 ys_2)))))
(assert (forall ((x_63 Nat_0) (z_5 Nat_0) (ys_2 list_0) (x_12 Nat_0))
	(=>	(and (diseqNat_0 x_12 z_5)
			(count_0 x_63 x_12 ys_2))
		(count_0 x_63 x_12 (cons_0 z_5 ys_2)))))
(assert (forall ((x_12 Nat_0))
	(count_0 zero_0 x_12 nil_0)))
(assert (forall ((x_66 Nat_0) (x_67 Nat_0) (x_68 Nat_0) (x_69 Nat_0) (x_13 Nat_0) (y_8 Nat_0) (z_6 Nat_0))
	(=>	(and (diseqNat_0 x_67 x_69)
			(plus_0 x_66 y_8 z_6)
			(plus_0 x_67 x_13 x_66)
			(plus_0 x_68 x_13 y_8)
			(plus_0 x_69 x_68 z_6))
		false)))
(assert (forall ((x_70 Nat_0) (x_71 Nat_0) (x_14 Nat_0) (y_9 Nat_0))
	(=>	(and (diseqNat_0 x_70 x_71)
			(plus_0 x_70 x_14 y_9)
			(plus_0 x_71 y_9 x_14))
		false)))
(assert (forall ((x_72 Nat_0) (x_15 Nat_0))
	(=>	(and (diseqNat_0 x_72 x_15)
			(plus_0 x_72 x_15 zero_0))
		false)))
(assert (forall ((x_73 Nat_0) (x_16 Nat_0))
	(=>	(and (diseqNat_0 x_73 x_16)
			(plus_0 x_73 zero_0 x_16))
		false)))
(assert (forall ((x_74 list_0) (x_75 Nat_0) (x_76 Nat_0) (x_17 Nat_0) (xs_3 list_0))
	(=>	(and (diseqNat_0 x_75 x_76)
			(msortbu_0 x_74 xs_3)
			(count_0 x_75 x_17 x_74)
			(count_0 x_76 x_17 xs_3))
		false)))
(check-sat)
