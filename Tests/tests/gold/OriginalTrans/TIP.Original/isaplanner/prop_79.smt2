(set-logic HORN)
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
(declare-fun x_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_3 Nat_0) (x_2 Nat_0) (z_1 Nat_0))
	(=> (x_0 x_3 z_1 x_2)
	    (x_0 x_3 (S_0 z_1) (S_0 x_2)))))
(assert (forall ((z_1 Nat_0))
	(x_0 (S_0 z_1) (S_0 z_1) Z_0)))
(assert (forall ((y_0 Nat_0))
	(x_0 Z_0 Z_0 y_0)))
(assert (forall ((x_7 Nat_0) (x_8 Nat_0) (x_9 Nat_0) (x_10 Nat_0) (m_0 Nat_0) (n_0 Nat_0) (k_0 Nat_0))
	(=>	(and (diseqNat_0 x_8 x_10)
			(x_0 x_7 (S_0 m_0) n_0)
			(x_0 x_8 x_7 (S_0 k_0))
			(x_0 x_9 m_0 n_0)
			(x_0 x_10 x_9 k_0))
		false)))
(check-sat)
