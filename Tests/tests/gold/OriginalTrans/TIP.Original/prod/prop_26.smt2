(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_17 Nat_0))
	(projS_1 x_17 (S_0 x_17))))
(assert (isZ_2 Z_0))
(assert (forall ((x_19 Nat_0))
	(isS_0 (S_0 x_19))))
(assert (forall ((x_20 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_20))))
(assert (forall ((x_21 Nat_0))
	(diseqNat_0 (S_0 x_21) Z_0)))
(assert (forall ((x_22 Nat_0) (x_23 Nat_0))
	(=> (diseqNat_0 x_22 x_23)
	    (diseqNat_0 (S_0 x_22) (S_0 x_23)))))
(declare-fun half_0 (Nat_0 Nat_0) Bool)
(assert (forall ((x_5 Nat_0) (z_1 Nat_0))
	(=> (half_0 x_5 z_1)
	    (half_0 (S_0 x_5) (S_0 (S_0 z_1))))))
(assert (half_0 Z_0 (S_0 Z_0)))
(assert (half_0 Z_0 Z_0))
(declare-fun x_1 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_9 Nat_0) (z_2 Nat_0) (y_1 Nat_0))
	(=> (x_1 x_9 z_2 y_1)
	    (x_1 (S_0 x_9) (S_0 z_2) y_1))))
(assert (forall ((x_10 Nat_0))
	(x_1 x_10 Z_0 x_10)))
(assert (forall ((x_11 Nat_0) (x_12 Nat_0) (x_13 Nat_0) (x_14 Nat_0) (x_3 Nat_0) (y_2 Nat_0))
	(=>	(and (diseqNat_0 x_12 x_14)
			(x_1 x_11 x_3 y_2)
			(half_0 x_12 x_11)
			(x_1 x_13 y_2 x_3)
			(half_0 x_14 x_13))
		false)))
(check-sat)
