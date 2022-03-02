(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_9 Nat_0))
	(projS_1 x_9 (S_0 x_9))))
(assert (isZ_2 Z_0))
(assert (forall ((x_11 Nat_0))
	(isS_0 (S_0 x_11))))
(assert (forall ((x_12 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_12))))
(assert (forall ((x_13 Nat_0))
	(diseqNat_0 (S_0 x_13) Z_0)))
(assert (forall ((x_14 Nat_0) (x_15 Nat_0))
	(=> (diseqNat_0 x_14 x_15)
	    (diseqNat_0 (S_0 x_14) (S_0 x_15)))))
(declare-fun min_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_2 Nat_0) (y_1 Nat_0) (z_1 Nat_0))
	(=> (min_0 x_2 z_1 y_1)
	    (min_0 (S_0 x_2) (S_0 z_1) (S_0 y_1)))))
(assert (forall ((z_1 Nat_0))
	(min_0 Z_0 (S_0 z_1) Z_0)))
(assert (forall ((y_0 Nat_0))
	(min_0 Z_0 Z_0 y_0)))
(assert (forall ((x_5 Nat_0) (x_6 Nat_0) (a_0 Nat_0) (b_0 Nat_0))
	(=>	(and (diseqNat_0 x_5 x_6)
			(min_0 x_5 a_0 b_0)
			(min_0 x_6 b_0 a_0))
		false)))
(check-sat)