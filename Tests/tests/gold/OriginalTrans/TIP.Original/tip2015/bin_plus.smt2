(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_1 ) (Z_2 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_41 Nat_0))
	(unS_1 x_41 (Z_2 x_41))))
(assert (isZ_2 Z_1))
(assert (forall ((x_43 Nat_0))
	(isZ_3 (Z_2 x_43))))
(assert (forall ((x_44 Nat_0))
	(diseqNat_0 Z_1 (Z_2 x_44))))
(assert (forall ((x_45 Nat_0))
	(diseqNat_0 (Z_2 x_45) Z_1)))
(assert (forall ((x_46 Nat_0) (x_47 Nat_0))
	(=> (diseqNat_0 x_46 x_47)
	    (diseqNat_0 (Z_2 x_46) (Z_2 x_47)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_2 Nat_0))
	(add_0 y_2 Z_1 y_2)))
(assert (forall ((r_0 Nat_0) (x_35 Nat_0) (y_2 Nat_0))
	(=> (add_0 r_0 x_35 y_2)
	    (add_0 (Z_2 r_0) (Z_2 x_35) y_2))))
(assert (forall ((y_2 Nat_0))
	(minus_0 Z_1 Z_1 y_2)))
(assert (forall ((r_0 Nat_0) (x_35 Nat_0) (y_2 Nat_0))
	(=> (minus_0 r_0 x_35 y_2)
	    (minus_0 (Z_2 r_0) (Z_2 x_35) y_2))))
(assert (forall ((y_2 Nat_0))
	(le_0 Z_1 y_2)))
(assert (forall ((x_35 Nat_0) (y_2 Nat_0))
	(=> (le_0 x_35 y_2)
	    (le_0 (Z_2 x_35) (Z_2 y_2)))))
(assert (forall ((y_2 Nat_0))
	(ge_0 y_2 Z_1)))
(assert (forall ((x_35 Nat_0) (y_2 Nat_0))
	(=> (ge_0 x_35 y_2)
	    (ge_0 (Z_2 x_35) (Z_2 y_2)))))
(assert (forall ((y_2 Nat_0))
	(lt_0 Z_1 (Z_2 y_2))))
(assert (forall ((x_35 Nat_0) (y_2 Nat_0))
	(=> (lt_0 x_35 y_2)
	    (lt_0 (Z_2 x_35) (Z_2 y_2)))))
(assert (forall ((y_2 Nat_0))
	(gt_0 (Z_2 y_2) Z_1)))
(assert (forall ((x_35 Nat_0) (y_2 Nat_0))
	(=> (gt_0 x_35 y_2)
	    (gt_0 (Z_2 x_35) (Z_2 y_2)))))
(assert (forall ((y_2 Nat_0))
	(mult_0 Z_1 Z_1 y_2)))
(assert (forall ((r_0 Nat_0) (x_35 Nat_0) (y_2 Nat_0) (z_3 Nat_0))
	(=>	(and (mult_0 r_0 x_35 y_2)
			(add_0 z_3 r_0 y_2))
		(mult_0 z_3 (Z_2 x_35) y_2))))
(assert (forall ((x_35 Nat_0) (y_2 Nat_0))
	(=> (lt_0 x_35 y_2)
	    (div_0 Z_1 x_35 y_2))))
(assert (forall ((r_0 Nat_0) (x_35 Nat_0) (y_2 Nat_0) (z_3 Nat_0))
	(=>	(and (ge_0 x_35 y_2)
			(minus_0 z_3 x_35 y_2)
			(div_0 r_0 z_3 y_2))
		(div_0 (Z_2 r_0) x_35 y_2))))
(assert (forall ((x_35 Nat_0) (y_2 Nat_0))
	(=> (lt_0 x_35 y_2)
	    (mod_0 x_35 x_35 y_2))))
(assert (forall ((r_0 Nat_0) (x_35 Nat_0) (y_2 Nat_0) (z_3 Nat_0))
	(=>	(and (ge_0 x_35 y_2)
			(minus_0 z_3 x_35 y_2)
			(mod_0 r_0 z_3 y_2))
		(mod_0 r_0 x_35 y_2))))
(declare-datatypes ((Bin_0 0)) (((One_0 ) (ZeroAnd_0 (projZeroAnd_0 Bin_0)) (OneAnd_0 (projOneAnd_0 Bin_0)))))
(declare-fun diseqBin_0 (Bin_0 Bin_0) Bool)
(declare-fun projZeroAnd_1 (Bin_0 Bin_0) Bool)
(declare-fun projOneAnd_1 (Bin_0 Bin_0) Bool)
(declare-fun isOne_0 (Bin_0) Bool)
(declare-fun isZeroAnd_0 (Bin_0) Bool)
(declare-fun isOneAnd_0 (Bin_0) Bool)
(assert (forall ((x_49 Bin_0))
	(projZeroAnd_1 x_49 (ZeroAnd_0 x_49))))
(assert (forall ((x_51 Bin_0))
	(projOneAnd_1 x_51 (OneAnd_0 x_51))))
(assert (isOne_0 One_0))
(assert (forall ((x_53 Bin_0))
	(isZeroAnd_0 (ZeroAnd_0 x_53))))
(assert (forall ((x_54 Bin_0))
	(isOneAnd_0 (OneAnd_0 x_54))))
(assert (forall ((x_55 Bin_0))
	(diseqBin_0 One_0 (ZeroAnd_0 x_55))))
(assert (forall ((x_56 Bin_0))
	(diseqBin_0 One_0 (OneAnd_0 x_56))))
(assert (forall ((x_57 Bin_0))
	(diseqBin_0 (ZeroAnd_0 x_57) One_0)))
(assert (forall ((x_58 Bin_0))
	(diseqBin_0 (OneAnd_0 x_58) One_0)))
(assert (forall ((x_59 Bin_0) (x_60 Bin_0))
	(diseqBin_0 (ZeroAnd_0 x_59) (OneAnd_0 x_60))))
(assert (forall ((x_61 Bin_0) (x_62 Bin_0))
	(diseqBin_0 (OneAnd_0 x_61) (ZeroAnd_0 x_62))))
(assert (forall ((x_63 Bin_0) (x_64 Bin_0))
	(=> (diseqBin_0 x_63 x_64)
	    (diseqBin_0 (ZeroAnd_0 x_63) (ZeroAnd_0 x_64)))))
(assert (forall ((x_65 Bin_0) (x_66 Bin_0))
	(=> (diseqBin_0 x_65 x_66)
	    (diseqBin_0 (OneAnd_0 x_65) (OneAnd_0 x_66)))))
(declare-fun toNat_0 (Nat_0 Bin_0) Bool)
(assert (forall ((x_36 Nat_0) (x_37 Nat_0) (x_6 Nat_0) (x_7 Nat_0) (ys_0 Bin_0))
	(=>	(and (toNat_0 x_6 ys_0)
			(toNat_0 x_7 ys_0)
			(add_0 x_36 (Z_2 Z_1) x_6)
			(add_0 x_37 x_36 x_7))
		(toNat_0 x_37 (OneAnd_0 ys_0)))))
(assert (forall ((x_38 Nat_0) (x_9 Nat_0) (x_10 Nat_0) (xs_0 Bin_0))
	(=>	(and (toNat_0 x_9 xs_0)
			(toNat_0 x_10 xs_0)
			(add_0 x_38 x_9 x_10))
		(toNat_0 x_38 (ZeroAnd_0 xs_0)))))
(assert (toNat_0 (Z_2 Z_1) One_0))
(declare-fun s_0 (Bin_0 Bin_0) Bool)
(assert (forall ((x_13 Bin_0) (ys_1 Bin_0))
	(=> (s_0 x_13 ys_1)
	    (s_0 (ZeroAnd_0 x_13) (OneAnd_0 ys_1)))))
(assert (forall ((xs_1 Bin_0))
	(s_0 (OneAnd_0 xs_1) (ZeroAnd_0 xs_1))))
(assert (s_0 (ZeroAnd_0 One_0) One_0))
(declare-fun plus_0 (Bin_0 Bin_0 Bin_0) Bool)
(assert (forall ((x_17 Bin_0) (x_18 Bin_0) (ys_3 Bin_0) (x_3 Bin_0))
	(=>	(and (plus_0 x_17 x_3 ys_3)
			(s_0 x_18 x_17))
		(plus_0 (ZeroAnd_0 x_18) (OneAnd_0 x_3) (OneAnd_0 ys_3)))))
(assert (forall ((x_20 Bin_0) (zs_0 Bin_0) (x_3 Bin_0))
	(=> (plus_0 x_20 x_3 zs_0)
	    (plus_0 (OneAnd_0 x_20) (OneAnd_0 x_3) (ZeroAnd_0 zs_0)))))
(assert (forall ((x_21 Bin_0) (x_3 Bin_0))
	(=> (s_0 x_21 (OneAnd_0 x_3))
	    (plus_0 x_21 (OneAnd_0 x_3) One_0))))
(assert (forall ((x_24 Bin_0) (xs_2 Bin_0) (z_0 Bin_0))
	(=> (plus_0 x_24 z_0 xs_2)
	    (plus_0 (OneAnd_0 x_24) (ZeroAnd_0 z_0) (OneAnd_0 xs_2)))))
(assert (forall ((x_26 Bin_0) (ys_2 Bin_0) (z_0 Bin_0))
	(=> (plus_0 x_26 z_0 ys_2)
	    (plus_0 (ZeroAnd_0 x_26) (ZeroAnd_0 z_0) (ZeroAnd_0 ys_2)))))
(assert (forall ((x_27 Bin_0) (z_0 Bin_0))
	(=> (s_0 x_27 (ZeroAnd_0 z_0))
	    (plus_0 x_27 (ZeroAnd_0 z_0) One_0))))
(assert (forall ((x_29 Bin_0) (y_0 Bin_0))
	(=> (s_0 x_29 y_0)
	    (plus_0 x_29 One_0 y_0))))
(assert (forall ((x_39 Nat_0) (x_31 Bin_0) (x_32 Nat_0) (x_33 Nat_0) (x_34 Nat_0) (x_4 Bin_0) (y_1 Bin_0))
	(=>	(and (diseqNat_0 x_32 x_39)
			(plus_0 x_31 x_4 y_1)
			(toNat_0 x_32 x_31)
			(toNat_0 x_33 x_4)
			(toNat_0 x_34 y_1)
			(add_0 x_39 x_33 x_34))
		false)))
(check-sat)
