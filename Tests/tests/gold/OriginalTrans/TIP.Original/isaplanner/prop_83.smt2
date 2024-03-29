(set-logic HORN)
(declare-datatypes ((Nat_1 0)) (((Z_6 ) (Z_7 (unS_0 Nat_1)))))
(declare-fun diseqNat_1 (Nat_1 Nat_1) Bool)
(declare-fun unS_1 (Nat_1 Nat_1) Bool)
(declare-fun isZ_3 (Nat_1) Bool)
(declare-fun isZ_4 (Nat_1) Bool)
(assert (forall ((x_92 Nat_1))
	(unS_1 x_92 (Z_7 x_92))))
(assert (isZ_3 Z_6))
(assert (forall ((x_94 Nat_1))
	(isZ_4 (Z_7 x_94))))
(assert (forall ((x_95 Nat_1))
	(diseqNat_1 Z_6 (Z_7 x_95))))
(assert (forall ((x_96 Nat_1))
	(diseqNat_1 (Z_7 x_96) Z_6)))
(assert (forall ((x_97 Nat_1) (x_98 Nat_1))
	(=> (diseqNat_1 x_97 x_98)
	    (diseqNat_1 (Z_7 x_97) (Z_7 x_98)))))
(declare-fun add_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun minus_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun le_0 (Nat_1 Nat_1) Bool)
(declare-fun ge_0 (Nat_1 Nat_1) Bool)
(declare-fun lt_0 (Nat_1 Nat_1) Bool)
(declare-fun gt_0 (Nat_1 Nat_1) Bool)
(declare-fun mult_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun div_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun mod_0 (Nat_1 Nat_1 Nat_1) Bool)
(assert (forall ((y_6 Nat_1))
	(add_0 y_6 Z_6 y_6)))
(assert (forall ((r_0 Nat_1) (x_45 Nat_1) (y_6 Nat_1))
	(=> (add_0 r_0 x_45 y_6)
	    (add_0 (Z_7 r_0) (Z_7 x_45) y_6))))
(assert (forall ((y_6 Nat_1))
	(minus_0 Z_6 Z_6 y_6)))
(assert (forall ((r_0 Nat_1) (x_45 Nat_1) (y_6 Nat_1))
	(=> (minus_0 r_0 x_45 y_6)
	    (minus_0 (Z_7 r_0) (Z_7 x_45) y_6))))
(assert (forall ((y_6 Nat_1))
	(le_0 Z_6 y_6)))
(assert (forall ((x_45 Nat_1) (y_6 Nat_1))
	(=> (le_0 x_45 y_6)
	    (le_0 (Z_7 x_45) (Z_7 y_6)))))
(assert (forall ((y_6 Nat_1))
	(ge_0 y_6 Z_6)))
(assert (forall ((x_45 Nat_1) (y_6 Nat_1))
	(=> (ge_0 x_45 y_6)
	    (ge_0 (Z_7 x_45) (Z_7 y_6)))))
(assert (forall ((y_6 Nat_1))
	(lt_0 Z_6 (Z_7 y_6))))
(assert (forall ((x_45 Nat_1) (y_6 Nat_1))
	(=> (lt_0 x_45 y_6)
	    (lt_0 (Z_7 x_45) (Z_7 y_6)))))
(assert (forall ((y_6 Nat_1))
	(gt_0 (Z_7 y_6) Z_6)))
(assert (forall ((x_45 Nat_1) (y_6 Nat_1))
	(=> (gt_0 x_45 y_6)
	    (gt_0 (Z_7 x_45) (Z_7 y_6)))))
(assert (forall ((y_6 Nat_1))
	(mult_0 Z_6 Z_6 y_6)))
(assert (forall ((r_0 Nat_1) (x_45 Nat_1) (y_6 Nat_1) (z_8 Nat_1))
	(=>	(and (mult_0 r_0 x_45 y_6)
			(add_0 z_8 r_0 y_6))
		(mult_0 z_8 (Z_7 x_45) y_6))))
(assert (forall ((x_45 Nat_1) (y_6 Nat_1))
	(=> (lt_0 x_45 y_6)
	    (div_0 Z_6 x_45 y_6))))
(assert (forall ((r_0 Nat_1) (x_45 Nat_1) (y_6 Nat_1) (z_8 Nat_1))
	(=>	(and (ge_0 x_45 y_6)
			(minus_0 z_8 x_45 y_6)
			(div_0 r_0 z_8 y_6))
		(div_0 (Z_7 r_0) x_45 y_6))))
(assert (forall ((x_45 Nat_1) (y_6 Nat_1))
	(=> (lt_0 x_45 y_6)
	    (mod_0 x_45 x_45 y_6))))
(assert (forall ((r_0 Nat_1) (x_45 Nat_1) (y_6 Nat_1) (z_8 Nat_1))
	(=>	(and (ge_0 x_45 y_6)
			(minus_0 z_8 x_45 y_6)
			(mod_0 r_0 z_8 y_6))
		(mod_0 r_0 x_45 y_6))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 Nat_1) (projpair_1 Nat_1)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (Nat_1 pair_0) Bool)
(declare-fun projpair_3 (Nat_1 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_46 Nat_1) (x_47 Nat_1))
	(projpair_2 x_46 (pair_1 x_46 x_47))))
(assert (forall ((x_46 Nat_1) (x_47 Nat_1))
	(projpair_3 x_47 (pair_1 x_46 x_47))))
(assert (forall ((x_49 Nat_1) (x_50 Nat_1))
	(ispair_0 (pair_1 x_49 x_50))))
(assert (forall ((x_51 Nat_1) (x_52 Nat_1) (x_53 Nat_1) (x_54 Nat_1))
	(=> (diseqNat_1 x_51 x_53)
	    (diseqpair_0 (pair_1 x_51 x_52) (pair_1 x_53 x_54)))))
(assert (forall ((x_51 Nat_1) (x_52 Nat_1) (x_53 Nat_1) (x_54 Nat_1))
	(=> (diseqNat_1 x_52 x_54)
	    (diseqpair_0 (pair_1 x_51 x_52) (pair_1 x_53 x_54)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_1) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_2 (Nat_1 list_0) Bool)
(declare-fun tail_2 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_56 Nat_1) (x_57 list_0))
	(head_2 x_56 (cons_0 x_56 x_57))))
(assert (forall ((x_56 Nat_1) (x_57 list_0))
	(tail_2 x_57 (cons_0 x_56 x_57))))
(assert (isnil_0 nil_0))
(assert (forall ((x_59 Nat_1) (x_60 list_0))
	(iscons_0 (cons_0 x_59 x_60))))
(assert (forall ((x_61 Nat_1) (x_62 list_0))
	(diseqlist_0 nil_0 (cons_0 x_61 x_62))))
(assert (forall ((x_63 Nat_1) (x_64 list_0))
	(diseqlist_0 (cons_0 x_63 x_64) nil_0)))
(assert (forall ((x_65 Nat_1) (x_66 list_0) (x_67 Nat_1) (x_68 list_0))
	(=> (diseqNat_1 x_65 x_67)
	    (diseqlist_0 (cons_0 x_65 x_66) (cons_0 x_67 x_68)))))
(assert (forall ((x_65 Nat_1) (x_66 list_0) (x_67 Nat_1) (x_68 list_0))
	(=> (diseqlist_0 x_66 x_68)
	    (diseqlist_0 (cons_0 x_65 x_66) (cons_0 x_67 x_68)))))
(declare-datatypes ((list_1 0)) (((nil_1 ) (cons_1 (head_1 pair_0) (tail_1 list_1)))))
(declare-fun diseqlist_1 (list_1 list_1) Bool)
(declare-fun head_3 (pair_0 list_1) Bool)
(declare-fun tail_3 (list_1 list_1) Bool)
(declare-fun isnil_1 (list_1) Bool)
(declare-fun iscons_1 (list_1) Bool)
(assert (forall ((x_70 pair_0) (x_71 list_1))
	(head_3 x_70 (cons_1 x_70 x_71))))
(assert (forall ((x_70 pair_0) (x_71 list_1))
	(tail_3 x_71 (cons_1 x_70 x_71))))
(assert (isnil_1 nil_1))
(assert (forall ((x_73 pair_0) (x_74 list_1))
	(iscons_1 (cons_1 x_73 x_74))))
(assert (forall ((x_75 pair_0) (x_76 list_1))
	(diseqlist_1 nil_1 (cons_1 x_75 x_76))))
(assert (forall ((x_77 pair_0) (x_78 list_1))
	(diseqlist_1 (cons_1 x_77 x_78) nil_1)))
(assert (forall ((x_79 pair_0) (x_80 list_1) (x_81 pair_0) (x_82 list_1))
	(=> (diseqpair_0 x_79 x_81)
	    (diseqlist_1 (cons_1 x_79 x_80) (cons_1 x_81 x_82)))))
(assert (forall ((x_79 pair_0) (x_80 list_1) (x_81 pair_0) (x_82 list_1))
	(=> (diseqlist_1 x_80 x_82)
	    (diseqlist_1 (cons_1 x_79 x_80) (cons_1 x_81 x_82)))))
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_84 Nat_0))
	(projS_1 x_84 (S_0 x_84))))
(assert (isZ_2 Z_0))
(assert (forall ((x_86 Nat_0))
	(isS_0 (S_0 x_86))))
(assert (forall ((x_87 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_87))))
(assert (forall ((x_88 Nat_0))
	(diseqNat_0 (S_0 x_88) Z_0)))
(assert (forall ((x_89 Nat_0) (x_90 Nat_0))
	(=> (diseqNat_0 x_89 x_90)
	    (diseqNat_0 (S_0 x_89) (S_0 x_90)))))
(declare-fun zip_0 (list_1 list_0 list_0) Bool)
(assert (forall ((x_16 list_1) (x_2 Nat_1) (x_3 list_0) (z_1 Nat_1) (x_1 list_0))
	(=> (zip_0 x_16 x_1 x_3)
	    (zip_0 (cons_1 (pair_1 z_1 x_2) x_16) (cons_0 z_1 x_1) (cons_0 x_2 x_3)))))
(assert (forall ((z_1 Nat_1) (x_1 list_0))
	(zip_0 nil_1 (cons_0 z_1 x_1) nil_0)))
(assert (forall ((y_0 list_0))
	(zip_0 nil_1 nil_0 y_0)))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_20 list_0) (x_5 Nat_1) (x_6 list_0) (z_2 Nat_0))
	(=> (take_0 x_20 z_2 x_6)
	    (take_0 (cons_0 x_5 x_20) (S_0 z_2) (cons_0 x_5 x_6)))))
(assert (forall ((z_2 Nat_0))
	(take_0 nil_0 (S_0 z_2) nil_0)))
(assert (forall ((y_1 list_0))
	(take_0 nil_0 Z_0 y_1)))
(declare-fun len_0 (Nat_0 list_0) Bool)
(assert (forall ((x_24 Nat_0) (y_2 Nat_1) (xs_0 list_0))
	(=> (len_0 x_24 xs_0)
	    (len_0 (S_0 x_24) (cons_0 y_2 xs_0)))))
(assert (len_0 Z_0 nil_0))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_26 list_0) (x_9 Nat_1) (x_10 list_0) (z_3 Nat_0))
	(=> (drop_0 x_26 z_3 x_10)
	    (drop_0 x_26 (S_0 z_3) (cons_0 x_9 x_10)))))
(assert (forall ((z_3 Nat_0))
	(drop_0 nil_0 (S_0 z_3) nil_0)))
(assert (forall ((x_29 list_0))
	(drop_0 x_29 Z_0 x_29)))
(declare-fun x_11 (list_0 list_0 list_0) Bool)
(assert (forall ((x_31 list_0) (z_4 Nat_1) (xs_1 list_0) (y_4 list_0))
	(=> (x_11 x_31 xs_1 y_4)
	    (x_11 (cons_0 z_4 x_31) (cons_0 z_4 xs_1) y_4))))
(assert (forall ((x_32 list_0))
	(x_11 x_32 nil_0 x_32)))
(declare-fun x_13 (list_1 list_1 list_1) Bool)
(assert (forall ((x_34 list_1) (z_5 pair_0) (xs_2 list_1) (y_5 list_1))
	(=> (x_13 x_34 xs_2 y_5)
	    (x_13 (cons_1 z_5 x_34) (cons_1 z_5 xs_2) y_5))))
(assert (forall ((x_35 list_1))
	(x_13 x_35 nil_1 x_35)))
(assert (forall ((x_36 list_0) (x_37 list_1) (x_38 Nat_0) (x_39 list_0) (x_40 list_1) (x_41 Nat_0) (x_42 list_0) (x_43 list_1) (x_44 list_1) (xs_3 list_0) (ys_0 list_0) (zs_0 list_0))
	(=>	(and (diseqlist_1 x_37 x_44)
			(x_11 x_36 xs_3 ys_0)
			(zip_0 x_37 x_36 zs_0)
			(len_0 x_38 xs_3)
			(take_0 x_39 x_38 zs_0)
			(zip_0 x_40 xs_3 x_39)
			(len_0 x_41 xs_3)
			(drop_0 x_42 x_41 zs_0)
			(zip_0 x_43 ys_0 x_42)
			(x_13 x_44 x_40 x_43))
		false)))
(check-sat)
