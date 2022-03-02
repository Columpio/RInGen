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
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_28 Nat_0))
	(projS_1 x_28 (S_0 x_28))))
(assert (isZ_2 Z_0))
(assert (forall ((x_30 Nat_0))
	(isS_0 (S_0 x_30))))
(assert (forall ((x_31 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_31))))
(assert (forall ((x_32 Nat_0))
	(diseqNat_0 (S_0 x_32) Z_0)))
(assert (forall ((x_33 Nat_0) (x_34 Nat_0))
	(=> (diseqNat_0 x_33 x_34)
	    (diseqNat_0 (S_0 x_33) (S_0 x_34)))))
(declare-fun max_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_9 Nat_0) (x_1 Nat_0) (z_1 Nat_0))
	(=> (max_0 x_9 z_1 x_1)
	    (max_0 (S_0 x_9) (S_0 z_1) (S_0 x_1)))))
(assert (forall ((z_1 Nat_0))
	(max_0 (S_0 z_1) (S_0 z_1) Z_0)))
(assert (forall ((x_11 Nat_0))
	(max_0 x_11 Z_0 x_11)))
(declare-fun x_2 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_12 Bool_0) (y_2 Nat_0) (x_4 Nat_0))
	(=> (x_2 x_12 x_4 y_2)
	    (x_2 x_12 (S_0 x_4) (S_0 y_2)))))
(assert (forall ((x_4 Nat_0))
	(x_2 false_0 (S_0 x_4) Z_0)))
(assert (forall ((z_2 Nat_0))
	(x_2 false_0 Z_0 (S_0 z_2))))
(assert (x_2 true_0 Z_0 Z_0))
(declare-fun x_5 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_17 Bool_0) (x_7 Nat_0) (z_3 Nat_0))
	(=> (x_5 x_17 z_3 x_7)
	    (x_5 x_17 (S_0 z_3) (S_0 x_7)))))
(assert (forall ((z_3 Nat_0))
	(x_5 false_0 (S_0 z_3) Z_0)))
(assert (forall ((y_3 Nat_0))
	(x_5 true_0 Z_0 y_3)))
(assert (forall ((x_21 Nat_0) (x_22 Bool_0) (x_23 Bool_0) (a_0 Nat_0) (b_0 Nat_0))
	(=>	(and (diseqBool_0 x_22 x_23)
			(max_0 x_21 a_0 b_0)
			(x_2 x_22 x_21 b_0)
			(x_5 x_23 a_0 b_0))
		false)))
(check-sat)