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
(assert (forall ((x_17 Nat_0))
	(p_1 x_17 (succ_0 x_17))))
(assert (iszero_0 zero_0))
(assert (forall ((x_19 Nat_0))
	(issucc_0 (succ_0 x_19))))
(assert (forall ((x_20 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_20))))
(assert (forall ((x_21 Nat_0))
	(diseqNat_0 (succ_0 x_21) zero_0)))
(assert (forall ((x_22 Nat_0) (x_23 Nat_0))
	(=> (diseqNat_0 x_22 x_23)
	    (diseqNat_0 (succ_0 x_22) (succ_0 x_23)))))
(declare-fun leq_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_4 Bool_0) (x_1 Nat_0) (z_0 Nat_0))
	(=> (leq_0 x_4 z_0 x_1)
	    (leq_0 x_4 (succ_0 z_0) (succ_0 x_1)))))
(assert (forall ((z_0 Nat_0))
	(leq_0 false_0 (succ_0 z_0) zero_0)))
(assert (forall ((y_0 Nat_0))
	(leq_0 true_0 zero_0 y_0)))
(declare-fun geq_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_8 Bool_0) (x_2 Nat_0) (y_1 Nat_0))
	(=> (leq_0 x_8 y_1 x_2)
	    (geq_0 x_8 x_2 y_1))))
(assert (forall ((x_10 Bool_0) (x_3 Nat_0) (y_2 Nat_0) (z_1 Nat_0))
	(=>	(and (diseqBool_0 x_10 true_0)
			(geq_0 true_0 x_3 y_2)
			(geq_0 true_0 y_2 z_1)
			(geq_0 x_10 x_3 z_1))
		false)))
(check-sat)
