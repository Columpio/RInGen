(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_10 Nat_0))
	(projS_1 x_10 (S_0 x_10))))
(assert (isZ_2 Z_0))
(assert (forall ((x_12 Nat_0))
	(isS_0 (S_0 x_12))))
(assert (forall ((x_13 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_13))))
(assert (forall ((x_14 Nat_0))
	(diseqNat_0 (S_0 x_14) Z_0)))
(assert (forall ((x_15 Nat_0) (x_16 Nat_0))
	(=> (diseqNat_0 x_15 x_16)
	    (diseqNat_0 (S_0 x_15) (S_0 x_16)))))
(declare-fun x_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_4 Nat_0) (z_1 Nat_0) (y_0 Nat_0))
	(=> (x_0 x_4 z_1 y_0)
	    (x_0 (S_0 x_4) (S_0 z_1) y_0))))
(assert (forall ((x_5 Nat_0))
	(x_0 x_5 Z_0 x_5)))
(assert (forall ((x_6 Nat_0) (x_7 Nat_0) (x_2 Nat_0))
	(=>	(and (diseqNat_0 x_6 (S_0 x_7))
			(x_0 x_6 x_2 (S_0 x_2))
			(x_0 x_7 x_2 x_2))
		false)))
(check-sat)