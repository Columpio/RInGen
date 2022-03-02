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
(assert (forall ((x_94 Nat_0))
	(p_1 x_94 (succ_0 x_94))))
(assert (iszero_0 zero_0))
(assert (forall ((x_96 Nat_0))
	(issucc_0 (succ_0 x_96))))
(assert (forall ((x_97 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_97))))
(assert (forall ((x_98 Nat_0))
	(diseqNat_0 (succ_0 x_98) zero_0)))
(assert (forall ((x_100 Nat_0) (x_99 Nat_0))
	(=> (diseqNat_0 x_99 x_100)
	    (diseqNat_0 (succ_0 x_99) (succ_0 x_100)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_102 Nat_0) (x_103 list_0))
	(head_1 x_102 (cons_0 x_102 x_103))))
(assert (forall ((x_102 Nat_0) (x_103 list_0))
	(tail_1 x_103 (cons_0 x_102 x_103))))
(assert (isnil_0 nil_0))
(assert (forall ((x_105 Nat_0) (x_106 list_0))
	(iscons_0 (cons_0 x_105 x_106))))
(assert (forall ((x_107 Nat_0) (x_108 list_0))
	(diseqlist_0 nil_0 (cons_0 x_107 x_108))))
(assert (forall ((x_109 Nat_0) (x_110 list_0))
	(diseqlist_0 (cons_0 x_109 x_110) nil_0)))
(assert (forall ((x_111 Nat_0) (x_112 list_0) (x_113 Nat_0) (x_114 list_0))
	(=> (diseqNat_0 x_111 x_113)
	    (diseqlist_0 (cons_0 x_111 x_112) (cons_0 x_113 x_114)))))
(assert (forall ((x_111 Nat_0) (x_112 list_0) (x_113 Nat_0) (x_114 list_0))
	(=> (diseqlist_0 x_112 x_114)
	    (diseqlist_0 (cons_0 x_111 x_112) (cons_0 x_113 x_114)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_23 list_0) (z_1 Nat_0) (xs_0 list_0) (z_0 Nat_0))
	(=> (take_0 x_23 z_0 xs_0)
	    (take_0 (cons_0 z_1 x_23) (succ_0 z_0) (cons_0 z_1 xs_0)))))
(assert (forall ((z_0 Nat_0))
	(take_0 nil_0 (succ_0 z_0) nil_0)))
(assert (forall ((y_0 list_0))
	(take_0 nil_0 zero_0 y_0)))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_27 Nat_0) (z_2 Nat_0) (y_1 Nat_0))
	(=> (plus_0 x_27 z_2 y_1)
	    (plus_0 (succ_0 x_27) (succ_0 z_2) y_1))))
(assert (forall ((x_28 Nat_0))
	(plus_0 x_28 zero_0 x_28)))
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_29 Nat_0) (y_3 Nat_0) (z_3 Nat_0))
	(=> (minus_0 x_29 z_3 y_3)
	    (minus_0 x_29 (succ_0 z_3) (succ_0 y_3)))))
(assert (forall ((z_3 Nat_0))
	(minus_0 zero_0 (succ_0 z_3) zero_0)))
(assert (forall ((y_2 Nat_0))
	(minus_0 zero_0 zero_0 y_2)))
(declare-fun lt_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_33 Bool_0) (n_0 Nat_0) (z_4 Nat_0))
	(=> (lt_0 x_33 n_0 z_4)
	    (lt_0 x_33 (succ_0 n_0) (succ_0 z_4)))))
(assert (forall ((z_4 Nat_0))
	(lt_0 true_0 zero_0 (succ_0 z_4))))
(assert (forall ((x_3 Nat_0))
	(lt_0 false_0 x_3 zero_0)))
(declare-fun leq_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_37 Bool_0) (x_5 Nat_0) (z_5 Nat_0))
	(=> (leq_0 x_37 z_5 x_5)
	    (leq_0 x_37 (succ_0 z_5) (succ_0 x_5)))))
(assert (forall ((z_5 Nat_0))
	(leq_0 false_0 (succ_0 z_5) zero_0)))
(assert (forall ((y_5 Nat_0))
	(leq_0 true_0 zero_0 y_5)))
(declare-fun lmerge_0 (list_0 list_0 list_0) Bool)
(assert (forall ((x_43 list_0) (x_8 Nat_0) (x_9 list_0) (z_6 Nat_0) (x_7 list_0))
	(=>	(and (lmerge_0 x_43 x_7 (cons_0 x_8 x_9))
			(leq_0 true_0 z_6 x_8))
		(lmerge_0 (cons_0 z_6 x_43) (cons_0 z_6 x_7) (cons_0 x_8 x_9)))))
(assert (forall ((x_46 list_0) (x_44 Bool_0) (x_8 Nat_0) (x_9 list_0) (z_6 Nat_0) (x_7 list_0))
	(=>	(and (diseqBool_0 x_44 true_0)
			(lmerge_0 x_46 (cons_0 z_6 x_7) x_9)
			(leq_0 x_44 z_6 x_8))
		(lmerge_0 (cons_0 x_8 x_46) (cons_0 z_6 x_7) (cons_0 x_8 x_9)))))
(assert (forall ((z_6 Nat_0) (x_7 list_0))
	(lmerge_0 (cons_0 z_6 x_7) (cons_0 z_6 x_7) nil_0)))
(assert (forall ((x_48 list_0))
	(lmerge_0 x_48 nil_0 x_48)))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_49 Nat_0) (x_50 Nat_0) (y_7 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_50 l_0)
			(plus_0 x_49 (succ_0 zero_0) x_50))
		(length_0 x_49 (cons_0 y_7 l_0)))))
(assert (length_0 zero_0 nil_0))
(declare-fun idiv_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_11 Nat_0) (y_8 Nat_0))
	(=> (lt_0 true_0 x_11 y_8)
	    (idiv_0 zero_0 x_11 y_8))))
(assert (forall ((x_57 Nat_0) (x_58 Nat_0) (x_55 Bool_0) (x_11 Nat_0) (y_8 Nat_0))
	(=>	(and (diseqBool_0 x_55 true_0)
			(minus_0 x_57 x_11 y_8)
			(idiv_0 x_58 x_57 y_8)
			(lt_0 x_55 x_11 y_8))
		(idiv_0 (succ_0 x_58) x_11 y_8))))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_59 list_0) (z_8 Nat_0) (xs_1 list_0) (z_7 Nat_0))
	(=> (drop_0 x_59 z_7 xs_1)
	    (drop_0 x_59 (succ_0 z_7) (cons_0 z_8 xs_1)))))
(assert (forall ((z_7 Nat_0))
	(drop_0 nil_0 (succ_0 z_7) nil_0)))
(assert (forall ((x_62 list_0))
	(drop_0 x_62 zero_0 x_62)))
(declare-fun msorttd_0 (list_0 list_0) Bool)
(assert (forall ((x_65 list_0) (x_66 list_0) (x_67 list_0) (x_68 list_0) (x_69 list_0) (x_63 Nat_0) (k_0 Nat_0) (x_14 Nat_0) (x_15 list_0) (y_10 Nat_0))
	(=>	(and (take_0 x_66 k_0 (cons_0 y_10 (cons_0 x_14 x_15)))
			(msorttd_0 x_67 x_66)
			(drop_0 x_68 k_0 (cons_0 y_10 (cons_0 x_14 x_15)))
			(msorttd_0 x_69 x_68)
			(lmerge_0 x_65 x_67 x_69)
			(length_0 x_63 (cons_0 y_10 (cons_0 x_14 x_15)))
			(idiv_0 k_0 x_63 (succ_0 (succ_0 zero_0))))
		(msorttd_0 x_65 (cons_0 y_10 (cons_0 x_14 x_15))))))
(assert (forall ((y_10 Nat_0))
	(msorttd_0 (cons_0 y_10 nil_0) (cons_0 y_10 nil_0))))
(assert (msorttd_0 nil_0 nil_0))
(declare-fun count_0 (Nat_0 Nat_0 list_0) Bool)
(assert (forall ((x_73 Nat_0) (x_74 Nat_0) (ys_0 list_0) (x_16 Nat_0))
	(=>	(and (count_0 x_74 x_16 ys_0)
			(plus_0 x_73 (succ_0 zero_0) x_74))
		(count_0 x_73 x_16 (cons_0 x_16 ys_0)))))
(assert (forall ((x_76 Nat_0) (z_10 Nat_0) (ys_0 list_0) (x_16 Nat_0))
	(=>	(and (diseqNat_0 x_16 z_10)
			(count_0 x_76 x_16 ys_0))
		(count_0 x_76 x_16 (cons_0 z_10 ys_0)))))
(assert (forall ((x_16 Nat_0))
	(count_0 zero_0 x_16 nil_0)))
(assert (forall ((x_79 Nat_0) (x_80 Nat_0) (x_81 Nat_0) (x_82 Nat_0) (x_17 Nat_0) (y_12 Nat_0) (z_11 Nat_0))
	(=>	(and (diseqNat_0 x_80 x_82)
			(plus_0 x_79 y_12 z_11)
			(plus_0 x_80 x_17 x_79)
			(plus_0 x_81 x_17 y_12)
			(plus_0 x_82 x_81 z_11))
		false)))
(assert (forall ((x_83 Nat_0) (x_84 Nat_0) (x_18 Nat_0) (y_13 Nat_0))
	(=>	(and (diseqNat_0 x_83 x_84)
			(plus_0 x_83 x_18 y_13)
			(plus_0 x_84 y_13 x_18))
		false)))
(assert (forall ((x_85 Nat_0) (x_19 Nat_0))
	(=>	(and (diseqNat_0 x_85 x_19)
			(plus_0 x_85 x_19 zero_0))
		false)))
(assert (forall ((x_86 Nat_0) (x_20 Nat_0))
	(=>	(and (diseqNat_0 x_86 x_20)
			(plus_0 x_86 zero_0 x_20))
		false)))
(assert (forall ((x_87 list_0) (x_88 Nat_0) (x_89 Nat_0) (x_21 Nat_0) (xs_2 list_0))
	(=>	(and (diseqNat_0 x_88 x_89)
			(msorttd_0 x_87 xs_2)
			(count_0 x_88 x_21 x_87)
			(count_0 x_89 x_21 xs_2))
		false)))
(check-sat)