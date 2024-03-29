(set-logic HORN)
(declare-datatypes ((Sign_0 0)) (((Pos_0 ) (Neg_0 ))))
(declare-fun diseqSign_0 (Sign_0 Sign_0) Bool)
(declare-fun isPos_0 (Sign_0) Bool)
(declare-fun isNeg_0 (Sign_0) Bool)
(assert (isPos_0 Pos_0))
(assert (isNeg_0 Neg_0))
(assert (diseqSign_0 Pos_0 Neg_0))
(assert (diseqSign_0 Neg_0 Pos_0))
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_2 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_85 Nat_0))
	(p_2 x_85 (succ_0 x_85))))
(assert (iszero_0 zero_0))
(assert (forall ((x_87 Nat_0))
	(issucc_0 (succ_0 x_87))))
(assert (forall ((x_88 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_88))))
(assert (forall ((x_89 Nat_0))
	(diseqNat_0 (succ_0 x_89) zero_0)))
(assert (forall ((x_90 Nat_0) (x_91 Nat_0))
	(=> (diseqNat_0 x_90 x_91)
	    (diseqNat_0 (succ_0 x_90) (succ_0 x_91)))))
(declare-datatypes ((Integer_0 0)) (((P_1 (projP_0 Nat_0)) (N_0 (projN_0 Nat_0)))))
(declare-fun diseqInteger_0 (Integer_0 Integer_0) Bool)
(declare-fun projP_1 (Nat_0 Integer_0) Bool)
(declare-fun projN_1 (Nat_0 Integer_0) Bool)
(declare-fun isP_0 (Integer_0) Bool)
(declare-fun isN_0 (Integer_0) Bool)
(assert (forall ((x_92 Nat_0))
	(projP_1 x_92 (P_1 x_92))))
(assert (forall ((x_94 Nat_0))
	(projN_1 x_94 (N_0 x_94))))
(assert (forall ((x_96 Nat_0))
	(isP_0 (P_1 x_96))))
(assert (forall ((x_97 Nat_0))
	(isN_0 (N_0 x_97))))
(assert (forall ((x_98 Nat_0) (x_99 Nat_0))
	(diseqInteger_0 (P_1 x_98) (N_0 x_99))))
(assert (forall ((x_100 Nat_0) (x_101 Nat_0))
	(diseqInteger_0 (N_0 x_100) (P_1 x_101))))
(assert (forall ((x_102 Nat_0) (x_103 Nat_0))
	(=> (diseqNat_0 x_102 x_103)
	    (diseqInteger_0 (P_1 x_102) (P_1 x_103)))))
(assert (forall ((x_104 Nat_0) (x_105 Nat_0))
	(=> (diseqNat_0 x_104 x_105)
	    (diseqInteger_0 (N_0 x_104) (N_0 x_105)))))
(declare-fun toInteger_0 (Integer_0 Sign_0 Nat_0) Bool)
(assert (forall ((z_0 Nat_0))
	(toInteger_0 (N_0 z_0) Neg_0 (succ_0 z_0))))
(assert (toInteger_0 (P_1 zero_0) Neg_0 zero_0))
(assert (forall ((y_0 Nat_0))
	(toInteger_0 (P_1 y_0) Pos_0 y_0)))
(declare-fun sign_1 (Sign_0 Integer_0) Bool)
(assert (forall ((z_1 Nat_0))
	(sign_1 Neg_0 (N_0 z_1))))
(assert (forall ((y_1 Nat_0))
	(sign_1 Pos_0 (P_1 y_1))))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_27 Nat_0) (z_2 Nat_0) (y_2 Nat_0))
	(=> (plus_0 x_27 z_2 y_2)
	    (plus_0 (succ_0 x_27) (succ_0 z_2) y_2))))
(assert (forall ((x_28 Nat_0))
	(plus_0 x_28 zero_0 x_28)))
(declare-fun times_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_29 Nat_0) (x_30 Nat_0) (z_3 Nat_0) (y_3 Nat_0))
	(=>	(and (times_0 x_30 z_3 y_3)
			(plus_0 x_29 y_3 x_30))
		(times_0 x_29 (succ_0 z_3) y_3))))
(assert (forall ((y_3 Nat_0))
	(times_0 zero_0 zero_0 y_3)))
(declare-fun opposite_0 (Sign_0 Sign_0) Bool)
(assert (opposite_0 Pos_0 Neg_0))
(assert (opposite_0 Neg_0 Pos_0))
(declare-fun timesSign_0 (Sign_0 Sign_0 Sign_0) Bool)
(assert (forall ((x_35 Sign_0) (y_4 Sign_0))
	(=> (opposite_0 x_35 y_4)
	    (timesSign_0 x_35 Neg_0 y_4))))
(assert (forall ((x_37 Sign_0))
	(timesSign_0 x_37 Pos_0 x_37)))
(declare-fun absVal_0 (Nat_0 Integer_0) Bool)
(assert (forall ((x_38 Nat_0) (m_0 Nat_0))
	(=> (plus_0 x_38 (succ_0 zero_0) m_0)
	    (absVal_0 x_38 (N_0 m_0)))))
(assert (forall ((n_1 Nat_0))
	(absVal_0 n_1 (P_1 n_1))))
(declare-fun times_1 (Integer_0 Integer_0 Integer_0) Bool)
(assert (forall ((x_41 Integer_0) (x_42 Sign_0) (x_43 Sign_0) (x_44 Sign_0) (x_45 Nat_0) (x_46 Nat_0) (x_47 Nat_0) (x_7 Integer_0) (y_5 Integer_0))
	(=>	(and (sign_1 x_42 x_7)
			(sign_1 x_43 y_5)
			(timesSign_0 x_44 x_42 x_43)
			(absVal_0 x_45 x_7)
			(absVal_0 x_46 y_5)
			(times_0 x_47 x_45 x_46)
			(toInteger_0 x_41 x_44 x_47))
		(times_1 x_41 x_7 y_5))))
(assert (forall ((x_49 Integer_0) (x_50 Integer_0) (x_51 Integer_0) (x_52 Integer_0) (x_8 Integer_0) (y_6 Integer_0) (z_4 Integer_0))
	(=>	(and (diseqInteger_0 x_50 x_52)
			(times_1 x_49 y_6 z_4)
			(times_1 x_50 x_8 x_49)
			(times_1 x_51 x_8 y_6)
			(times_1 x_52 x_51 z_4))
		false)))
(assert (forall ((x_53 Nat_0) (x_54 Nat_0) (x_55 Nat_0) (x_56 Nat_0) (x_9 Nat_0) (y_7 Nat_0) (z_5 Nat_0))
	(=>	(and (diseqNat_0 x_54 x_56)
			(times_0 x_53 y_7 z_5)
			(times_0 x_54 x_9 x_53)
			(times_0 x_55 x_9 y_7)
			(times_0 x_56 x_55 z_5))
		false)))
(assert (forall ((x_57 Nat_0) (x_58 Nat_0) (x_59 Nat_0) (x_60 Nat_0) (x_10 Nat_0) (y_8 Nat_0) (z_6 Nat_0))
	(=>	(and (diseqNat_0 x_58 x_60)
			(plus_0 x_57 y_8 z_6)
			(plus_0 x_58 x_10 x_57)
			(plus_0 x_59 x_10 y_8)
			(plus_0 x_60 x_59 z_6))
		false)))
(assert (forall ((x_61 Nat_0) (x_62 Nat_0) (x_11 Nat_0) (y_9 Nat_0))
	(=>	(and (diseqNat_0 x_61 x_62)
			(times_0 x_61 x_11 y_9)
			(times_0 x_62 y_9 x_11))
		false)))
(assert (forall ((x_63 Nat_0) (x_64 Nat_0) (x_12 Nat_0) (y_10 Nat_0))
	(=>	(and (diseqNat_0 x_63 x_64)
			(plus_0 x_63 x_12 y_10)
			(plus_0 x_64 y_10 x_12))
		false)))
(assert (forall ((x_65 Nat_0) (x_66 Nat_0) (x_67 Nat_0) (x_68 Nat_0) (x_69 Nat_0) (x_13 Nat_0) (y_11 Nat_0) (z_7 Nat_0))
	(=>	(and (diseqNat_0 x_66 x_69)
			(plus_0 x_65 y_11 z_7)
			(times_0 x_66 x_13 x_65)
			(times_0 x_67 x_13 y_11)
			(times_0 x_68 x_13 z_7)
			(plus_0 x_69 x_67 x_68))
		false)))
(assert (forall ((x_70 Nat_0) (x_71 Nat_0) (x_72 Nat_0) (x_73 Nat_0) (x_74 Nat_0) (x_14 Nat_0) (y_12 Nat_0) (z_8 Nat_0))
	(=>	(and (diseqNat_0 x_71 x_74)
			(plus_0 x_70 x_14 y_12)
			(times_0 x_71 x_70 z_8)
			(times_0 x_72 x_14 z_8)
			(times_0 x_73 y_12 z_8)
			(plus_0 x_74 x_72 x_73))
		false)))
(assert (forall ((x_75 Nat_0) (x_15 Nat_0))
	(=>	(and (diseqNat_0 x_75 x_15)
			(times_0 x_75 x_15 (succ_0 zero_0)))
		false)))
(assert (forall ((x_76 Nat_0) (x_16 Nat_0))
	(=>	(and (diseqNat_0 x_76 x_16)
			(times_0 x_76 (succ_0 zero_0) x_16))
		false)))
(assert (forall ((x_77 Nat_0) (x_17 Nat_0))
	(=>	(and (diseqNat_0 x_77 x_17)
			(plus_0 x_77 x_17 zero_0))
		false)))
(assert (forall ((x_78 Nat_0) (x_18 Nat_0))
	(=>	(and (diseqNat_0 x_78 x_18)
			(plus_0 x_78 zero_0 x_18))
		false)))
(assert (forall ((x_79 Nat_0) (x_19 Nat_0))
	(=>	(and (diseqNat_0 x_79 zero_0)
			(times_0 x_79 x_19 zero_0))
		false)))
(assert (forall ((x_80 Nat_0) (x_20 Nat_0))
	(=>	(and (diseqNat_0 x_80 zero_0)
			(times_0 x_80 zero_0 x_20))
		false)))
(check-sat)
