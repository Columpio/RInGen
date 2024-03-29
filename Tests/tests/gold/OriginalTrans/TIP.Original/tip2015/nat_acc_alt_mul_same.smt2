(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_1 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_66 Nat_0))
	(p_1 x_66 (succ_0 x_66))))
(assert (iszero_0 zero_0))
(assert (forall ((x_68 Nat_0))
	(issucc_0 (succ_0 x_68))))
(assert (forall ((x_69 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_69))))
(assert (forall ((x_70 Nat_0))
	(diseqNat_0 (succ_0 x_70) zero_0)))
(assert (forall ((x_71 Nat_0) (x_72 Nat_0))
	(=> (diseqNat_0 x_71 x_72)
	    (diseqNat_0 (succ_0 x_71) (succ_0 x_72)))))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_19 Nat_0) (z_0 Nat_0) (y_0 Nat_0))
	(=> (plus_0 x_19 z_0 y_0)
	    (plus_0 (succ_0 x_19) (succ_0 z_0) y_0))))
(assert (forall ((x_20 Nat_0))
	(plus_0 x_20 zero_0 x_20)))
(declare-fun times_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_21 Nat_0) (x_22 Nat_0) (z_1 Nat_0) (y_1 Nat_0))
	(=>	(and (times_0 x_22 z_1 y_1)
			(plus_0 x_21 y_1 x_22))
		(times_0 x_21 (succ_0 z_1) y_1))))
(assert (forall ((y_1 Nat_0))
	(times_0 zero_0 zero_0 y_1)))
(declare-fun accplus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_25 Nat_0) (z_2 Nat_0) (y_2 Nat_0))
	(=> (accplus_0 x_25 z_2 (succ_0 y_2))
	    (accplus_0 x_25 (succ_0 z_2) y_2))))
(assert (forall ((x_27 Nat_0))
	(accplus_0 x_27 zero_0 x_27)))
(declare-fun accaltmul_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_28 Nat_0) (x_29 Nat_0) (x_30 Nat_0) (x_4 Nat_0) (z_3 Nat_0))
	(=>	(and (accaltmul_0 x_29 z_3 x_4)
			(accplus_0 x_30 x_4 x_29)
			(accplus_0 x_28 (succ_0 z_3) x_30))
		(accaltmul_0 x_28 (succ_0 z_3) (succ_0 x_4)))))
(assert (forall ((z_3 Nat_0))
	(accaltmul_0 zero_0 (succ_0 z_3) zero_0)))
(assert (forall ((y_3 Nat_0))
	(accaltmul_0 zero_0 zero_0 y_3)))
(assert (forall ((x_34 Nat_0) (x_35 Nat_0) (x_5 Nat_0) (y_4 Nat_0))
	(=>	(and (diseqNat_0 x_34 x_35)
			(accaltmul_0 x_34 x_5 y_4)
			(times_0 x_35 x_5 y_4))
		false)))
(assert (forall ((x_36 Nat_0) (x_37 Nat_0) (x_38 Nat_0) (x_39 Nat_0) (x_6 Nat_0) (y_5 Nat_0) (z_4 Nat_0))
	(=>	(and (diseqNat_0 x_37 x_39)
			(times_0 x_36 y_5 z_4)
			(times_0 x_37 x_6 x_36)
			(times_0 x_38 x_6 y_5)
			(times_0 x_39 x_38 z_4))
		false)))
(assert (forall ((x_40 Nat_0) (x_41 Nat_0) (x_42 Nat_0) (x_43 Nat_0) (x_7 Nat_0) (y_6 Nat_0) (z_5 Nat_0))
	(=>	(and (diseqNat_0 x_41 x_43)
			(plus_0 x_40 y_6 z_5)
			(plus_0 x_41 x_7 x_40)
			(plus_0 x_42 x_7 y_6)
			(plus_0 x_43 x_42 z_5))
		false)))
(assert (forall ((x_44 Nat_0) (x_45 Nat_0) (x_8 Nat_0) (y_7 Nat_0))
	(=>	(and (diseqNat_0 x_44 x_45)
			(times_0 x_44 x_8 y_7)
			(times_0 x_45 y_7 x_8))
		false)))
(assert (forall ((x_46 Nat_0) (x_47 Nat_0) (x_9 Nat_0) (y_8 Nat_0))
	(=>	(and (diseqNat_0 x_46 x_47)
			(plus_0 x_46 x_9 y_8)
			(plus_0 x_47 y_8 x_9))
		false)))
(assert (forall ((x_48 Nat_0) (x_49 Nat_0) (x_50 Nat_0) (x_51 Nat_0) (x_52 Nat_0) (x_10 Nat_0) (y_9 Nat_0) (z_6 Nat_0))
	(=>	(and (diseqNat_0 x_49 x_52)
			(plus_0 x_48 y_9 z_6)
			(times_0 x_49 x_10 x_48)
			(times_0 x_50 x_10 y_9)
			(times_0 x_51 x_10 z_6)
			(plus_0 x_52 x_50 x_51))
		false)))
(assert (forall ((x_53 Nat_0) (x_54 Nat_0) (x_55 Nat_0) (x_56 Nat_0) (x_57 Nat_0) (x_11 Nat_0) (y_10 Nat_0) (z_7 Nat_0))
	(=>	(and (diseqNat_0 x_54 x_57)
			(plus_0 x_53 x_11 y_10)
			(times_0 x_54 x_53 z_7)
			(times_0 x_55 x_11 z_7)
			(times_0 x_56 y_10 z_7)
			(plus_0 x_57 x_55 x_56))
		false)))
(assert (forall ((x_58 Nat_0) (x_12 Nat_0))
	(=>	(and (diseqNat_0 x_58 x_12)
			(times_0 x_58 x_12 (succ_0 zero_0)))
		false)))
(assert (forall ((x_59 Nat_0) (x_13 Nat_0))
	(=>	(and (diseqNat_0 x_59 x_13)
			(times_0 x_59 (succ_0 zero_0) x_13))
		false)))
(assert (forall ((x_60 Nat_0) (x_14 Nat_0))
	(=>	(and (diseqNat_0 x_60 x_14)
			(plus_0 x_60 x_14 zero_0))
		false)))
(assert (forall ((x_61 Nat_0) (x_15 Nat_0))
	(=>	(and (diseqNat_0 x_61 x_15)
			(plus_0 x_61 zero_0 x_15))
		false)))
(assert (forall ((x_62 Nat_0) (x_16 Nat_0))
	(=>	(and (diseqNat_0 x_62 zero_0)
			(times_0 x_62 x_16 zero_0))
		false)))
(assert (forall ((x_63 Nat_0) (x_17 Nat_0))
	(=>	(and (diseqNat_0 x_63 zero_0)
			(times_0 x_63 zero_0 x_17))
		false)))
(check-sat)
