(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_1 ) (Z_2 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_48 Nat_0))
	(unS_1 x_48 (Z_2 x_48))))
(assert (isZ_2 Z_1))
(assert (forall ((x_50 Nat_0))
	(isZ_3 (Z_2 x_50))))
(assert (forall ((x_51 Nat_0))
	(diseqNat_0 Z_1 (Z_2 x_51))))
(assert (forall ((x_52 Nat_0))
	(diseqNat_0 (Z_2 x_52) Z_1)))
(assert (forall ((x_53 Nat_0) (x_54 Nat_0))
	(=> (diseqNat_0 x_53 x_54)
	    (diseqNat_0 (Z_2 x_53) (Z_2 x_54)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_3 Nat_0))
	(add_0 y_3 Z_1 y_3)))
(assert (forall ((r_0 Nat_0) (x_42 Nat_0) (y_3 Nat_0))
	(=> (add_0 r_0 x_42 y_3)
	    (add_0 (Z_2 r_0) (Z_2 x_42) y_3))))
(assert (forall ((y_3 Nat_0))
	(minus_0 Z_1 Z_1 y_3)))
(assert (forall ((r_0 Nat_0) (x_42 Nat_0) (y_3 Nat_0))
	(=> (minus_0 r_0 x_42 y_3)
	    (minus_0 (Z_2 r_0) (Z_2 x_42) y_3))))
(assert (forall ((y_3 Nat_0))
	(le_0 Z_1 y_3)))
(assert (forall ((x_42 Nat_0) (y_3 Nat_0))
	(=> (le_0 x_42 y_3)
	    (le_0 (Z_2 x_42) (Z_2 y_3)))))
(assert (forall ((y_3 Nat_0))
	(ge_0 y_3 Z_1)))
(assert (forall ((x_42 Nat_0) (y_3 Nat_0))
	(=> (ge_0 x_42 y_3)
	    (ge_0 (Z_2 x_42) (Z_2 y_3)))))
(assert (forall ((y_3 Nat_0))
	(lt_0 Z_1 (Z_2 y_3))))
(assert (forall ((x_42 Nat_0) (y_3 Nat_0))
	(=> (lt_0 x_42 y_3)
	    (lt_0 (Z_2 x_42) (Z_2 y_3)))))
(assert (forall ((y_3 Nat_0))
	(gt_0 (Z_2 y_3) Z_1)))
(assert (forall ((x_42 Nat_0) (y_3 Nat_0))
	(=> (gt_0 x_42 y_3)
	    (gt_0 (Z_2 x_42) (Z_2 y_3)))))
(assert (forall ((y_3 Nat_0))
	(mult_0 Z_1 Z_1 y_3)))
(assert (forall ((r_0 Nat_0) (x_42 Nat_0) (y_3 Nat_0) (z_3 Nat_0))
	(=>	(and (mult_0 r_0 x_42 y_3)
			(add_0 z_3 r_0 y_3))
		(mult_0 z_3 (Z_2 x_42) y_3))))
(assert (forall ((x_42 Nat_0) (y_3 Nat_0))
	(=> (lt_0 x_42 y_3)
	    (div_0 Z_1 x_42 y_3))))
(assert (forall ((r_0 Nat_0) (x_42 Nat_0) (y_3 Nat_0) (z_3 Nat_0))
	(=>	(and (ge_0 x_42 y_3)
			(minus_0 z_3 x_42 y_3)
			(div_0 r_0 z_3 y_3))
		(div_0 (Z_2 r_0) x_42 y_3))))
(assert (forall ((x_42 Nat_0) (y_3 Nat_0))
	(=> (lt_0 x_42 y_3)
	    (mod_0 x_42 x_42 y_3))))
(assert (forall ((r_0 Nat_0) (x_42 Nat_0) (y_3 Nat_0) (z_3 Nat_0))
	(=>	(and (ge_0 x_42 y_3)
			(minus_0 z_3 x_42 y_3)
			(mod_0 r_0 z_3 y_3))
		(mod_0 r_0 x_42 y_3))))
(declare-datatypes ((Bin_0 0)) (((One_0 ) (ZeroAnd_0 (projZeroAnd_0 Bin_0)) (OneAnd_0 (projOneAnd_0 Bin_0)))))
(declare-fun diseqBin_0 (Bin_0 Bin_0) Bool)
(declare-fun projZeroAnd_1 (Bin_0 Bin_0) Bool)
(declare-fun projOneAnd_1 (Bin_0 Bin_0) Bool)
(declare-fun isOne_0 (Bin_0) Bool)
(declare-fun isZeroAnd_0 (Bin_0) Bool)
(declare-fun isOneAnd_0 (Bin_0) Bool)
(assert (forall ((x_56 Bin_0))
	(projZeroAnd_1 x_56 (ZeroAnd_0 x_56))))
(assert (forall ((x_58 Bin_0))
	(projOneAnd_1 x_58 (OneAnd_0 x_58))))
(assert (isOne_0 One_0))
(assert (forall ((x_60 Bin_0))
	(isZeroAnd_0 (ZeroAnd_0 x_60))))
(assert (forall ((x_61 Bin_0))
	(isOneAnd_0 (OneAnd_0 x_61))))
(assert (forall ((x_62 Bin_0))
	(diseqBin_0 One_0 (ZeroAnd_0 x_62))))
(assert (forall ((x_63 Bin_0))
	(diseqBin_0 One_0 (OneAnd_0 x_63))))
(assert (forall ((x_64 Bin_0))
	(diseqBin_0 (ZeroAnd_0 x_64) One_0)))
(assert (forall ((x_65 Bin_0))
	(diseqBin_0 (OneAnd_0 x_65) One_0)))
(assert (forall ((x_66 Bin_0) (x_67 Bin_0))
	(diseqBin_0 (ZeroAnd_0 x_66) (OneAnd_0 x_67))))
(assert (forall ((x_68 Bin_0) (x_69 Bin_0))
	(diseqBin_0 (OneAnd_0 x_68) (ZeroAnd_0 x_69))))
(assert (forall ((x_70 Bin_0) (x_71 Bin_0))
	(=> (diseqBin_0 x_70 x_71)
	    (diseqBin_0 (ZeroAnd_0 x_70) (ZeroAnd_0 x_71)))))
(assert (forall ((x_72 Bin_0) (x_73 Bin_0))
	(=> (diseqBin_0 x_72 x_73)
	    (diseqBin_0 (OneAnd_0 x_72) (OneAnd_0 x_73)))))
(declare-fun toNat_0 (Nat_0 Bin_0) Bool)
(assert (forall ((x_43 Nat_0) (x_44 Nat_0) (x_7 Nat_0) (x_8 Nat_0) (ys_0 Bin_0))
	(=>	(and (toNat_0 x_7 ys_0)
			(toNat_0 x_8 ys_0)
			(add_0 x_43 (Z_2 Z_1) x_7)
			(add_0 x_44 x_43 x_8))
		(toNat_0 x_44 (OneAnd_0 ys_0)))))
(assert (forall ((x_45 Nat_0) (x_10 Nat_0) (x_11 Nat_0) (xs_0 Bin_0))
	(=>	(and (toNat_0 x_10 xs_0)
			(toNat_0 x_11 xs_0)
			(add_0 x_45 x_10 x_11))
		(toNat_0 x_45 (ZeroAnd_0 xs_0)))))
(assert (toNat_0 (Z_2 Z_1) One_0))
(declare-fun s_0 (Bin_0 Bin_0) Bool)
(assert (forall ((x_14 Bin_0) (ys_1 Bin_0))
	(=> (s_0 x_14 ys_1)
	    (s_0 (ZeroAnd_0 x_14) (OneAnd_0 ys_1)))))
(assert (forall ((xs_1 Bin_0))
	(s_0 (OneAnd_0 xs_1) (ZeroAnd_0 xs_1))))
(assert (s_0 (ZeroAnd_0 One_0) One_0))
(declare-fun plus_0 (Bin_0 Bin_0 Bin_0) Bool)
(assert (forall ((x_18 Bin_0) (x_19 Bin_0) (ys_3 Bin_0) (x_3 Bin_0))
	(=>	(and (plus_0 x_18 x_3 ys_3)
			(s_0 x_19 x_18))
		(plus_0 (ZeroAnd_0 x_19) (OneAnd_0 x_3) (OneAnd_0 ys_3)))))
(assert (forall ((x_21 Bin_0) (zs_0 Bin_0) (x_3 Bin_0))
	(=> (plus_0 x_21 x_3 zs_0)
	    (plus_0 (OneAnd_0 x_21) (OneAnd_0 x_3) (ZeroAnd_0 zs_0)))))
(assert (forall ((x_22 Bin_0) (x_3 Bin_0))
	(=> (s_0 x_22 (OneAnd_0 x_3))
	    (plus_0 x_22 (OneAnd_0 x_3) One_0))))
(assert (forall ((x_25 Bin_0) (xs_2 Bin_0) (z_0 Bin_0))
	(=> (plus_0 x_25 z_0 xs_2)
	    (plus_0 (OneAnd_0 x_25) (ZeroAnd_0 z_0) (OneAnd_0 xs_2)))))
(assert (forall ((x_27 Bin_0) (ys_2 Bin_0) (z_0 Bin_0))
	(=> (plus_0 x_27 z_0 ys_2)
	    (plus_0 (ZeroAnd_0 x_27) (ZeroAnd_0 z_0) (ZeroAnd_0 ys_2)))))
(assert (forall ((x_28 Bin_0) (z_0 Bin_0))
	(=> (s_0 x_28 (ZeroAnd_0 z_0))
	    (plus_0 x_28 (ZeroAnd_0 z_0) One_0))))
(assert (forall ((x_30 Bin_0) (y_0 Bin_0))
	(=> (s_0 x_30 y_0)
	    (plus_0 x_30 One_0 y_0))))
(declare-fun times_0 (Bin_0 Bin_0 Bin_0) Bool)
(assert (forall ((x_32 Bin_0) (x_33 Bin_0) (xs_4 Bin_0) (y_1 Bin_0))
	(=>	(and (times_0 x_33 xs_4 y_1)
			(plus_0 x_32 (ZeroAnd_0 x_33) y_1))
		(times_0 x_32 (OneAnd_0 xs_4) y_1))))
(assert (forall ((x_36 Bin_0) (xs_3 Bin_0) (y_1 Bin_0))
	(=> (times_0 x_36 xs_3 y_1)
	    (times_0 (ZeroAnd_0 x_36) (ZeroAnd_0 xs_3) y_1))))
(assert (forall ((x_37 Bin_0))
	(times_0 x_37 One_0 x_37)))
(assert (forall ((x_46 Nat_0) (x_38 Bin_0) (x_39 Nat_0) (x_40 Nat_0) (x_41 Nat_0) (x_5 Bin_0) (y_2 Bin_0))
	(=>	(and (diseqNat_0 x_39 x_46)
			(times_0 x_38 x_5 y_2)
			(toNat_0 x_39 x_38)
			(toNat_0 x_40 x_5)
			(toNat_0 x_41 y_2)
			(mult_0 x_46 x_40 x_41))
		false)))
(check-sat)