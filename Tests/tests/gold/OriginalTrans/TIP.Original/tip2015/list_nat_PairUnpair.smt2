(set-logic HORN)
(declare-datatypes ((Nat_1 0)) (((Z_4 ) (Z_5 (unS_0 Nat_1)))))
(declare-fun diseqNat_1 (Nat_1 Nat_1) Bool)
(declare-fun unS_1 (Nat_1 Nat_1) Bool)
(declare-fun isZ_2 (Nat_1) Bool)
(declare-fun isZ_3 (Nat_1) Bool)
(assert (forall ((x_92 Nat_1))
	(unS_1 x_92 (Z_5 x_92))))
(assert (isZ_2 Z_4))
(assert (forall ((x_94 Nat_1))
	(isZ_3 (Z_5 x_94))))
(assert (forall ((x_95 Nat_1))
	(diseqNat_1 Z_4 (Z_5 x_95))))
(assert (forall ((x_96 Nat_1))
	(diseqNat_1 (Z_5 x_96) Z_4)))
(assert (forall ((x_97 Nat_1) (x_98 Nat_1))
	(=> (diseqNat_1 x_97 x_98)
	    (diseqNat_1 (Z_5 x_97) (Z_5 x_98)))))
(declare-fun add_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun minus_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun le_0 (Nat_1 Nat_1) Bool)
(declare-fun ge_0 (Nat_1 Nat_1) Bool)
(declare-fun lt_0 (Nat_1 Nat_1) Bool)
(declare-fun gt_0 (Nat_1 Nat_1) Bool)
(declare-fun mult_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun div_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun mod_0 (Nat_1 Nat_1 Nat_1) Bool)
(assert (forall ((y_9 Nat_1))
	(add_0 y_9 Z_4 y_9)))
(assert (forall ((r_0 Nat_1) (x_43 Nat_1) (y_9 Nat_1))
	(=> (add_0 r_0 x_43 y_9)
	    (add_0 (Z_5 r_0) (Z_5 x_43) y_9))))
(assert (forall ((y_9 Nat_1))
	(minus_0 Z_4 Z_4 y_9)))
(assert (forall ((r_0 Nat_1) (x_43 Nat_1) (y_9 Nat_1))
	(=> (minus_0 r_0 x_43 y_9)
	    (minus_0 (Z_5 r_0) (Z_5 x_43) y_9))))
(assert (forall ((y_9 Nat_1))
	(le_0 Z_4 y_9)))
(assert (forall ((x_43 Nat_1) (y_9 Nat_1))
	(=> (le_0 x_43 y_9)
	    (le_0 (Z_5 x_43) (Z_5 y_9)))))
(assert (forall ((y_9 Nat_1))
	(ge_0 y_9 Z_4)))
(assert (forall ((x_43 Nat_1) (y_9 Nat_1))
	(=> (ge_0 x_43 y_9)
	    (ge_0 (Z_5 x_43) (Z_5 y_9)))))
(assert (forall ((y_9 Nat_1))
	(lt_0 Z_4 (Z_5 y_9))))
(assert (forall ((x_43 Nat_1) (y_9 Nat_1))
	(=> (lt_0 x_43 y_9)
	    (lt_0 (Z_5 x_43) (Z_5 y_9)))))
(assert (forall ((y_9 Nat_1))
	(gt_0 (Z_5 y_9) Z_4)))
(assert (forall ((x_43 Nat_1) (y_9 Nat_1))
	(=> (gt_0 x_43 y_9)
	    (gt_0 (Z_5 x_43) (Z_5 y_9)))))
(assert (forall ((y_9 Nat_1))
	(mult_0 Z_4 Z_4 y_9)))
(assert (forall ((r_0 Nat_1) (x_43 Nat_1) (y_9 Nat_1) (z_6 Nat_1))
	(=>	(and (mult_0 r_0 x_43 y_9)
			(add_0 z_6 r_0 y_9))
		(mult_0 z_6 (Z_5 x_43) y_9))))
(assert (forall ((x_43 Nat_1) (y_9 Nat_1))
	(=> (lt_0 x_43 y_9)
	    (div_0 Z_4 x_43 y_9))))
(assert (forall ((r_0 Nat_1) (x_43 Nat_1) (y_9 Nat_1) (z_6 Nat_1))
	(=>	(and (ge_0 x_43 y_9)
			(minus_0 z_6 x_43 y_9)
			(div_0 r_0 z_6 y_9))
		(div_0 (Z_5 r_0) x_43 y_9))))
(assert (forall ((x_43 Nat_1) (y_9 Nat_1))
	(=> (lt_0 x_43 y_9)
	    (mod_0 x_43 x_43 y_9))))
(assert (forall ((r_0 Nat_1) (x_43 Nat_1) (y_9 Nat_1) (z_6 Nat_1))
	(=>	(and (ge_0 x_43 y_9)
			(minus_0 z_6 x_43 y_9)
			(mod_0 r_0 z_6 y_9))
		(mod_0 r_0 x_43 y_9))))
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
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 Nat_1) (projpair_1 Nat_1)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (Nat_1 pair_0) Bool)
(declare-fun projpair_3 (Nat_1 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_46 Nat_1) (x_47 Nat_1))
	(projpair_2 x_46 (pair_1 x_46 x_47))))
(assert (forall ((x_46 Nat_1) (x_47 Nat_1))
	(projpair_3 x_47 (pair_1 x_46 x_47))))
(assert (forall ((x_49 Nat_1) (x_50 Nat_1))
	(ispair_0 (pair_1 x_49 x_50))))
(assert (forall ((x_51 Nat_1) (x_52 Nat_1) (x_53 Nat_1) (x_54 Nat_1))
	(=> (diseqNat_1 x_51 x_53)
	    (diseqpair_0 (pair_1 x_51 x_52) (pair_1 x_53 x_54)))))
(assert (forall ((x_51 Nat_1) (x_52 Nat_1) (x_53 Nat_1) (x_54 Nat_1))
	(=> (diseqNat_1 x_52 x_54)
	    (diseqpair_0 (pair_1 x_51 x_52) (pair_1 x_53 x_54)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_1) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_2 (Nat_1 list_0) Bool)
(declare-fun tail_2 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_56 Nat_1) (x_57 list_0))
	(head_2 x_56 (cons_0 x_56 x_57))))
(assert (forall ((x_56 Nat_1) (x_57 list_0))
	(tail_2 x_57 (cons_0 x_56 x_57))))
(assert (isnil_0 nil_0))
(assert (forall ((x_59 Nat_1) (x_60 list_0))
	(iscons_0 (cons_0 x_59 x_60))))
(assert (forall ((x_61 Nat_1) (x_62 list_0))
	(diseqlist_0 nil_0 (cons_0 x_61 x_62))))
(assert (forall ((x_63 Nat_1) (x_64 list_0))
	(diseqlist_0 (cons_0 x_63 x_64) nil_0)))
(assert (forall ((x_65 Nat_1) (x_66 list_0) (x_67 Nat_1) (x_68 list_0))
	(=> (diseqNat_1 x_65 x_67)
	    (diseqlist_0 (cons_0 x_65 x_66) (cons_0 x_67 x_68)))))
(assert (forall ((x_65 Nat_1) (x_66 list_0) (x_67 Nat_1) (x_68 list_0))
	(=> (diseqlist_0 x_66 x_68)
	    (diseqlist_0 (cons_0 x_65 x_66) (cons_0 x_67 x_68)))))
(declare-datatypes ((list_1 0)) (((nil_1 ) (cons_1 (head_1 pair_0) (tail_1 list_1)))))
(declare-fun diseqlist_1 (list_1 list_1) Bool)
(declare-fun head_3 (pair_0 list_1) Bool)
(declare-fun tail_3 (list_1 list_1) Bool)
(declare-fun isnil_1 (list_1) Bool)
(declare-fun iscons_1 (list_1) Bool)
(assert (forall ((x_70 pair_0) (x_71 list_1))
	(head_3 x_70 (cons_1 x_70 x_71))))
(assert (forall ((x_70 pair_0) (x_71 list_1))
	(tail_3 x_71 (cons_1 x_70 x_71))))
(assert (isnil_1 nil_1))
(assert (forall ((x_73 pair_0) (x_74 list_1))
	(iscons_1 (cons_1 x_73 x_74))))
(assert (forall ((x_75 pair_0) (x_76 list_1))
	(diseqlist_1 nil_1 (cons_1 x_75 x_76))))
(assert (forall ((x_77 pair_0) (x_78 list_1))
	(diseqlist_1 (cons_1 x_77 x_78) nil_1)))
(assert (forall ((x_79 pair_0) (x_80 list_1) (x_81 pair_0) (x_82 list_1))
	(=> (diseqpair_0 x_79 x_81)
	    (diseqlist_1 (cons_1 x_79 x_80) (cons_1 x_81 x_82)))))
(assert (forall ((x_79 pair_0) (x_80 list_1) (x_81 pair_0) (x_82 list_1))
	(=> (diseqlist_1 x_80 x_82)
	    (diseqlist_1 (cons_1 x_79 x_80) (cons_1 x_81 x_82)))))
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_1 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_84 Nat_0))
	(p_1 x_84 (succ_0 x_84))))
(assert (iszero_0 zero_0))
(assert (forall ((x_86 Nat_0))
	(issucc_0 (succ_0 x_86))))
(assert (forall ((x_87 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_87))))
(assert (forall ((x_88 Nat_0))
	(diseqNat_0 (succ_0 x_88) zero_0)))
(assert (forall ((x_89 Nat_0) (x_90 Nat_0))
	(=> (diseqNat_0 x_89 x_90)
	    (diseqNat_0 (succ_0 x_89) (succ_0 x_90)))))
(declare-fun unpair_0 (list_0 list_1) Bool)
(assert (forall ((x_10 list_0) (z_0 Nat_1) (y_1 Nat_1) (xys_0 list_1))
	(=> (unpair_0 x_10 xys_0)
	    (unpair_0 (cons_0 z_0 (cons_0 y_1 x_10)) (cons_1 (pair_1 z_0 y_1) xys_0)))))
(assert (unpair_0 nil_0 nil_1))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_13 Nat_0) (z_1 Nat_0) (y_2 Nat_0))
	(=> (plus_0 x_13 z_1 y_2)
	    (plus_0 (succ_0 x_13) (succ_0 z_1) y_2))))
(assert (forall ((x_14 Nat_0))
	(plus_0 x_14 zero_0 x_14)))
(declare-fun pairs_0 (list_1 list_0) Bool)
(assert (forall ((x_16 list_1) (y_4 Nat_1) (xs_0 list_0) (y_3 Nat_1))
	(=> (pairs_0 x_16 xs_0)
	    (pairs_0 (cons_1 (pair_1 y_3 y_4) x_16) (cons_0 y_3 (cons_0 y_4 xs_0))))))
(assert (forall ((y_3 Nat_1))
	(pairs_0 nil_1 (cons_0 y_3 nil_0))))
(assert (pairs_0 nil_1 nil_0))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_19 Nat_0) (x_20 Nat_0) (y_5 Nat_1) (l_0 list_0))
	(=>	(and (length_0 x_20 l_0)
			(plus_0 x_19 (succ_0 zero_0) x_20))
		(length_0 x_19 (cons_0 y_5 l_0)))))
(assert (length_0 zero_0 nil_0))
(declare-fun even_0 (Bool_0 Nat_0) Bool)
(assert (forall ((x_23 Bool_0) (x_24 Bool_0) (y_6 Nat_0))
	(=>	(and (even_0 x_24 y_6)
			(not_0 x_23 x_24))
		(even_0 x_23 (succ_0 y_6)))))
(assert (even_0 true_0 zero_0))
(assert (forall ((x_26 Nat_0) (x_27 Nat_0) (x_28 Nat_0) (x_29 Nat_0) (x_5 Nat_0) (y_7 Nat_0) (z_3 Nat_0))
	(=>	(and (diseqNat_0 x_27 x_29)
			(plus_0 x_26 y_7 z_3)
			(plus_0 x_27 x_5 x_26)
			(plus_0 x_28 x_5 y_7)
			(plus_0 x_29 x_28 z_3))
		false)))
(assert (forall ((x_30 Nat_0) (x_31 Nat_0) (x_6 Nat_0) (y_8 Nat_0))
	(=>	(and (diseqNat_0 x_30 x_31)
			(plus_0 x_30 x_6 y_8)
			(plus_0 x_31 y_8 x_6))
		false)))
(assert (forall ((x_32 Nat_0) (x_7 Nat_0))
	(=>	(and (diseqNat_0 x_32 x_7)
			(plus_0 x_32 x_7 zero_0))
		false)))
(assert (forall ((x_33 Nat_0) (x_8 Nat_0))
	(=>	(and (diseqNat_0 x_33 x_8)
			(plus_0 x_33 zero_0 x_8))
		false)))
(assert (forall ((x_36 Nat_0) (x_34 list_1) (x_35 list_0) (xs_1 list_0))
	(=>	(and (diseqlist_0 x_35 xs_1)
			(length_0 x_36 xs_1)
			(even_0 true_0 x_36)
			(pairs_0 x_34 xs_1)
			(unpair_0 x_35 x_34))
		false)))
(check-sat)