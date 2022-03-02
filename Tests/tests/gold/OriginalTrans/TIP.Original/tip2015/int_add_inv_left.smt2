(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_2 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_57 Nat_0))
	(p_2 x_57 (succ_0 x_57))))
(assert (iszero_0 zero_0))
(assert (forall ((x_59 Nat_0))
	(issucc_0 (succ_0 x_59))))
(assert (forall ((x_60 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_60))))
(assert (forall ((x_61 Nat_0))
	(diseqNat_0 (succ_0 x_61) zero_0)))
(assert (forall ((x_62 Nat_0) (x_63 Nat_0))
	(=> (diseqNat_0 x_62 x_63)
	    (diseqNat_0 (succ_0 x_62) (succ_0 x_63)))))
(declare-datatypes ((Integer_0 0)) (((P_1 (projP_0 Nat_0)) (N_0 (projN_0 Nat_0)))))
(declare-fun diseqInteger_0 (Integer_0 Integer_0) Bool)
(declare-fun projP_1 (Nat_0 Integer_0) Bool)
(declare-fun projN_1 (Nat_0 Integer_0) Bool)
(declare-fun isP_0 (Integer_0) Bool)
(declare-fun isN_0 (Integer_0) Bool)
(assert (forall ((x_64 Nat_0))
	(projP_1 x_64 (P_1 x_64))))
(assert (forall ((x_66 Nat_0))
	(projN_1 x_66 (N_0 x_66))))
(assert (forall ((x_68 Nat_0))
	(isP_0 (P_1 x_68))))
(assert (forall ((x_69 Nat_0))
	(isN_0 (N_0 x_69))))
(assert (forall ((x_70 Nat_0) (x_71 Nat_0))
	(diseqInteger_0 (P_1 x_70) (N_0 x_71))))
(assert (forall ((x_72 Nat_0) (x_73 Nat_0))
	(diseqInteger_0 (N_0 x_72) (P_1 x_73))))
(assert (forall ((x_74 Nat_0) (x_75 Nat_0))
	(=> (diseqNat_0 x_74 x_75)
	    (diseqInteger_0 (P_1 x_74) (P_1 x_75)))))
(assert (forall ((x_76 Nat_0) (x_77 Nat_0))
	(=> (diseqNat_0 x_76 x_77)
	    (diseqInteger_0 (N_0 x_76) (N_0 x_77)))))
(declare-fun zero_1 (Integer_0) Bool)
(assert (zero_1 (P_1 zero_0)))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_15 Nat_0) (z_0 Nat_0) (y_0 Nat_0))
	(=> (plus_0 x_15 z_0 y_0)
	    (plus_0 (succ_0 x_15) (succ_0 z_0) y_0))))
(assert (forall ((x_16 Nat_0))
	(plus_0 x_16 zero_0 x_16)))
(declare-fun neg_0 (Integer_0 Integer_0) Bool)
(assert (forall ((x_18 Nat_0) (n_1 Nat_0))
	(=> (plus_0 x_18 (succ_0 zero_0) n_1)
	    (neg_0 (P_1 x_18) (N_0 n_1)))))
(assert (forall ((z_1 Nat_0))
	(neg_0 (N_0 z_1) (P_1 (succ_0 z_1)))))
(assert (neg_0 (P_1 zero_0) (P_1 zero_0)))
(declare-fun x_2 (Integer_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_4 Nat_0) (z_2 Nat_0) (fail_0 Integer_0))
	(=> (x_2 fail_0 x_4 z_2)
	    (x_2 fail_0 (succ_0 x_4) (succ_0 z_2)))))
(assert (forall ((x_5 Nat_0))
	(x_2 (N_0 (succ_0 x_5)) zero_0 (succ_0 x_5))))
(assert (forall ((x_6 Nat_0))
	(x_2 (P_1 (succ_0 x_6)) (succ_0 x_6) zero_0)))
(assert (x_2 (P_1 zero_0) zero_0 zero_0))
(declare-fun plus_1 (Integer_0 Integer_0 Integer_0) Bool)
(assert (forall ((x_34 Nat_0) (x_35 Nat_0) (n_4 Nat_0) (m_1 Nat_0))
	(=>	(and (plus_0 x_34 (succ_0 zero_0) m_1)
			(plus_0 x_35 x_34 n_4))
		(plus_1 (N_0 x_35) (N_0 m_1) (N_0 n_4)))))
(assert (forall ((x_36 Integer_0) (x_37 Nat_0) (n_3 Nat_0) (m_1 Nat_0))
	(=>	(and (plus_0 x_37 (succ_0 zero_0) m_1)
			(x_2 x_36 n_3 x_37))
		(plus_1 x_36 (N_0 m_1) (P_1 n_3)))))
(assert (forall ((x_39 Integer_0) (x_40 Nat_0) (o_0 Nat_0) (m_0 Nat_0))
	(=>	(and (plus_0 x_40 (succ_0 zero_0) o_0)
			(x_2 x_39 m_0 x_40))
		(plus_1 x_39 (P_1 m_0) (N_0 o_0)))))
(assert (forall ((x_43 Nat_0) (n_2 Nat_0) (m_0 Nat_0))
	(=> (plus_0 x_43 m_0 n_2)
	    (plus_1 (P_1 x_43) (P_1 m_0) (P_1 n_2)))))
(assert (forall ((x_44 Integer_0) (x_45 Integer_0) (x_46 Integer_0) (x_8 Integer_0))
	(=>	(and (diseqInteger_0 x_45 x_46)
			(neg_0 x_44 x_8)
			(plus_1 x_45 x_44 x_8)
			(zero_1 x_46))
		false)))
(assert (forall ((x_47 Nat_0) (x_48 Nat_0) (x_49 Nat_0) (x_50 Nat_0) (x_9 Nat_0) (y_4 Nat_0) (z_3 Nat_0))
	(=>	(and (diseqNat_0 x_48 x_50)
			(plus_0 x_47 y_4 z_3)
			(plus_0 x_48 x_9 x_47)
			(plus_0 x_49 x_9 y_4)
			(plus_0 x_50 x_49 z_3))
		false)))
(assert (forall ((x_51 Nat_0) (x_52 Nat_0) (x_10 Nat_0) (y_5 Nat_0))
	(=>	(and (diseqNat_0 x_51 x_52)
			(plus_0 x_51 x_10 y_5)
			(plus_0 x_52 y_5 x_10))
		false)))
(assert (forall ((x_53 Nat_0) (x_11 Nat_0))
	(=>	(and (diseqNat_0 x_53 x_11)
			(plus_0 x_53 x_11 zero_0))
		false)))
(assert (forall ((x_54 Nat_0) (x_12 Nat_0))
	(=>	(and (diseqNat_0 x_54 x_12)
			(plus_0 x_54 zero_0 x_12))
		false)))
(check-sat)