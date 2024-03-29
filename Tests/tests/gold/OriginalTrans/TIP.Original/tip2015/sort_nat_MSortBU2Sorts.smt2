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
(assert (forall ((x_63 Nat_0))
	(p_1 x_63 (succ_0 x_63))))
(assert (iszero_0 zero_0))
(assert (forall ((x_65 Nat_0))
	(issucc_0 (succ_0 x_65))))
(assert (forall ((x_66 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_66))))
(assert (forall ((x_67 Nat_0))
	(diseqNat_0 (succ_0 x_67) zero_0)))
(assert (forall ((x_68 Nat_0) (x_69 Nat_0))
	(=> (diseqNat_0 x_68 x_69)
	    (diseqNat_0 (succ_0 x_68) (succ_0 x_69)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_2 (Nat_0 list_0) Bool)
(declare-fun tail_2 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_71 Nat_0) (x_72 list_0))
	(head_2 x_71 (cons_0 x_71 x_72))))
(assert (forall ((x_71 Nat_0) (x_72 list_0))
	(tail_2 x_72 (cons_0 x_71 x_72))))
(assert (isnil_0 nil_0))
(assert (forall ((x_74 Nat_0) (x_75 list_0))
	(iscons_0 (cons_0 x_74 x_75))))
(assert (forall ((x_76 Nat_0) (x_77 list_0))
	(diseqlist_0 nil_0 (cons_0 x_76 x_77))))
(assert (forall ((x_78 Nat_0) (x_79 list_0))
	(diseqlist_0 (cons_0 x_78 x_79) nil_0)))
(assert (forall ((x_80 Nat_0) (x_81 list_0) (x_82 Nat_0) (x_83 list_0))
	(=> (diseqNat_0 x_80 x_82)
	    (diseqlist_0 (cons_0 x_80 x_81) (cons_0 x_82 x_83)))))
(assert (forall ((x_80 Nat_0) (x_81 list_0) (x_82 Nat_0) (x_83 list_0))
	(=> (diseqlist_0 x_81 x_83)
	    (diseqlist_0 (cons_0 x_80 x_81) (cons_0 x_82 x_83)))))
(declare-datatypes ((list_1 0)) (((nil_1 ) (cons_1 (head_1 list_0) (tail_1 list_1)))))
(declare-fun diseqlist_1 (list_1 list_1) Bool)
(declare-fun head_3 (list_0 list_1) Bool)
(declare-fun tail_3 (list_1 list_1) Bool)
(declare-fun isnil_1 (list_1) Bool)
(declare-fun iscons_1 (list_1) Bool)
(assert (forall ((x_85 list_0) (x_86 list_1))
	(head_3 x_85 (cons_1 x_85 x_86))))
(assert (forall ((x_85 list_0) (x_86 list_1))
	(tail_3 x_86 (cons_1 x_85 x_86))))
(assert (isnil_1 nil_1))
(assert (forall ((x_88 list_0) (x_89 list_1))
	(iscons_1 (cons_1 x_88 x_89))))
(assert (forall ((x_90 list_0) (x_91 list_1))
	(diseqlist_1 nil_1 (cons_1 x_90 x_91))))
(assert (forall ((x_92 list_0) (x_93 list_1))
	(diseqlist_1 (cons_1 x_92 x_93) nil_1)))
(assert (forall ((x_94 list_0) (x_95 list_1) (x_96 list_0) (x_97 list_1))
	(=> (diseqlist_0 x_94 x_96)
	    (diseqlist_1 (cons_1 x_94 x_95) (cons_1 x_96 x_97)))))
(assert (forall ((x_94 list_0) (x_95 list_1) (x_96 list_0) (x_97 list_1))
	(=> (diseqlist_1 x_95 x_97)
	    (diseqlist_1 (cons_1 x_94 x_95) (cons_1 x_96 x_97)))))
(declare-fun leq_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_12 Bool_0) (x_1 Nat_0) (z_0 Nat_0))
	(=> (leq_0 x_12 z_0 x_1)
	    (leq_0 x_12 (succ_0 z_0) (succ_0 x_1)))))
(assert (forall ((z_0 Nat_0))
	(leq_0 false_0 (succ_0 z_0) zero_0)))
(assert (forall ((y_0 Nat_0))
	(leq_0 true_0 zero_0 y_0)))
(declare-fun lmerge_0 (list_0 list_0 list_0) Bool)
(assert (forall ((x_18 list_0) (x_4 Nat_0) (x_5 list_0) (z_1 Nat_0) (x_3 list_0))
	(=>	(and (lmerge_0 x_18 x_3 (cons_0 x_4 x_5))
			(leq_0 true_0 z_1 x_4))
		(lmerge_0 (cons_0 z_1 x_18) (cons_0 z_1 x_3) (cons_0 x_4 x_5)))))
(assert (forall ((x_21 list_0) (x_19 Bool_0) (x_4 Nat_0) (x_5 list_0) (z_1 Nat_0) (x_3 list_0))
	(=>	(and (diseqBool_0 x_19 true_0)
			(lmerge_0 x_21 (cons_0 z_1 x_3) x_5)
			(leq_0 x_19 z_1 x_4))
		(lmerge_0 (cons_0 x_4 x_21) (cons_0 z_1 x_3) (cons_0 x_4 x_5)))))
(assert (forall ((z_1 Nat_0) (x_3 list_0))
	(lmerge_0 (cons_0 z_1 x_3) (cons_0 z_1 x_3) nil_0)))
(assert (forall ((x_23 list_0))
	(lmerge_0 x_23 nil_0 x_23)))
(declare-fun pairwise_0 (list_1 list_1) Bool)
(assert (forall ((x_25 list_0) (x_26 list_1) (ys_0 list_0) (xss_0 list_1) (xs_0 list_0))
	(=>	(and (lmerge_0 x_25 xs_0 ys_0)
			(pairwise_0 x_26 xss_0))
		(pairwise_0 (cons_1 x_25 x_26) (cons_1 xs_0 (cons_1 ys_0 xss_0))))))
(assert (forall ((xs_0 list_0))
	(pairwise_0 (cons_1 xs_0 nil_1) (cons_1 xs_0 nil_1))))
(assert (pairwise_0 nil_1 nil_1))
(declare-fun mergingbu_0 (list_0 list_1) Bool)
(assert (forall ((x_29 list_0) (x_30 list_1) (z_2 list_0) (x_8 list_1) (xs_1 list_0))
	(=>	(and (pairwise_0 x_30 (cons_1 xs_1 (cons_1 z_2 x_8)))
			(mergingbu_0 x_29 x_30))
		(mergingbu_0 x_29 (cons_1 xs_1 (cons_1 z_2 x_8))))))
(assert (forall ((x_32 list_0))
	(mergingbu_0 x_32 (cons_1 x_32 nil_1))))
(assert (mergingbu_0 nil_0 nil_1))
(declare-fun ordered_0 (Bool_0 list_0) Bool)
(assert (forall ((x_34 Bool_0) (x_35 Bool_0) (x_36 Bool_0) (y_5 Nat_0) (xs_2 list_0) (y_4 Nat_0))
	(=>	(and (leq_0 x_35 y_4 y_5)
			(ordered_0 x_36 (cons_0 y_5 xs_2))
			(and_0 x_34 x_35 x_36))
		(ordered_0 x_34 (cons_0 y_4 (cons_0 y_5 xs_2))))))
(assert (forall ((y_4 Nat_0))
	(ordered_0 true_0 (cons_0 y_4 nil_0))))
(assert (ordered_0 true_0 nil_0))
(declare-fun risers_0 (list_1 list_0) Bool)
(assert (forall ((ys_1 list_0) (yss_0 list_1) (y_7 Nat_0) (xs_3 list_0) (y_6 Nat_0))
	(=>	(and (risers_0 (cons_1 ys_1 yss_0) (cons_0 y_7 xs_3))
			(leq_0 true_0 y_6 y_7))
		(risers_0 (cons_1 (cons_0 y_6 ys_1) yss_0) (cons_0 y_6 (cons_0 y_7 xs_3))))))
(assert (forall ((x_44 list_1) (x_42 Bool_0) (y_7 Nat_0) (xs_3 list_0) (y_6 Nat_0))
	(=>	(and (diseqBool_0 x_42 true_0)
			(risers_0 x_44 (cons_0 y_7 xs_3))
			(leq_0 x_42 y_6 y_7))
		(risers_0 (cons_1 (cons_0 y_6 nil_0) x_44) (cons_0 y_6 (cons_0 y_7 xs_3))))))
(assert (forall ((y_7 Nat_0) (xs_3 list_0) (y_6 Nat_0))
	(=>	(and (risers_0 nil_1 (cons_0 y_7 xs_3))
			(leq_0 true_0 y_6 y_7))
		(risers_0 nil_1 (cons_0 y_6 (cons_0 y_7 xs_3))))))
(assert (forall ((x_50 list_1) (x_48 Bool_0) (y_7 Nat_0) (xs_3 list_0) (y_6 Nat_0))
	(=>	(and (diseqBool_0 x_48 true_0)
			(risers_0 x_50 (cons_0 y_7 xs_3))
			(leq_0 x_48 y_6 y_7))
		(risers_0 (cons_1 (cons_0 y_6 nil_0) x_50) (cons_0 y_6 (cons_0 y_7 xs_3))))))
(assert (forall ((y_6 Nat_0))
	(risers_0 (cons_1 (cons_0 y_6 nil_0) nil_1) (cons_0 y_6 nil_0))))
(assert (risers_0 nil_1 nil_0))
(declare-fun msortbu_0 (list_0 list_0) Bool)
(assert (forall ((x_53 list_0) (x_54 list_1) (x_11 list_0))
	(=>	(and (risers_0 x_54 x_11)
			(mergingbu_0 x_53 x_54))
		(msortbu_0 x_53 x_11))))
(assert (forall ((x_56 list_0) (x_57 Bool_0) (xs_4 list_0))
	(=>	(and (diseqBool_0 x_57 true_0)
			(msortbu_0 x_56 xs_4)
			(ordered_0 x_57 x_56))
		false)))
(check-sat)
