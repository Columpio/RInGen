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
(assert (forall ((x_13 Nat_0))
	(projS_1 x_13 (S_0 x_13))))
(assert (isZ_2 Z_0))
(assert (forall ((x_15 Nat_0))
	(isS_0 (S_0 x_15))))
(assert (forall ((x_16 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_16))))
(assert (forall ((x_17 Nat_0))
	(diseqNat_0 (S_0 x_17) Z_0)))
(assert (forall ((x_18 Nat_0) (x_19 Nat_0))
	(=> (diseqNat_0 x_18 x_19)
	    (diseqNat_0 (S_0 x_18) (S_0 x_19)))))
(declare-fun x_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_3 Bool_0) (x_2 Nat_0) (z_1 Nat_0))
	(=> (x_0 x_3 z_1 x_2)
	    (x_0 x_3 (S_0 z_1) (S_0 x_2)))))
(assert (forall ((z_1 Nat_0))
	(x_0 false_0 (S_0 z_1) Z_0)))
(assert (forall ((y_0 Nat_0))
	(x_0 true_0 Z_0 y_0)))
(assert (forall ((x_7 Bool_0) (m_0 Nat_0) (n_0 Nat_0))
	(=>	(and (diseqBool_0 x_7 true_0)
			(x_0 true_0 m_0 n_0)
			(x_0 x_7 m_0 (S_0 n_0)))
		false)))
(check-sat)
