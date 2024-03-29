(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_5 ) (Z_6 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_60 Nat_0))
	(unS_1 x_60 (Z_6 x_60))))
(assert (isZ_2 Z_5))
(assert (forall ((x_62 Nat_0))
	(isZ_3 (Z_6 x_62))))
(assert (forall ((x_63 Nat_0))
	(diseqNat_0 Z_5 (Z_6 x_63))))
(assert (forall ((x_64 Nat_0))
	(diseqNat_0 (Z_6 x_64) Z_5)))
(assert (forall ((x_65 Nat_0) (x_66 Nat_0))
	(=> (diseqNat_0 x_65 x_66)
	    (diseqNat_0 (Z_6 x_65) (Z_6 x_66)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_7 Nat_0))
	(add_0 y_7 Z_5 y_7)))
(assert (forall ((r_0 Nat_0) (x_53 Nat_0) (y_7 Nat_0))
	(=> (add_0 r_0 x_53 y_7)
	    (add_0 (Z_6 r_0) (Z_6 x_53) y_7))))
(assert (forall ((y_7 Nat_0))
	(minus_0 Z_5 Z_5 y_7)))
(assert (forall ((r_0 Nat_0) (x_53 Nat_0) (y_7 Nat_0))
	(=> (minus_0 r_0 x_53 y_7)
	    (minus_0 (Z_6 r_0) (Z_6 x_53) y_7))))
(assert (forall ((y_7 Nat_0))
	(le_0 Z_5 y_7)))
(assert (forall ((x_53 Nat_0) (y_7 Nat_0))
	(=> (le_0 x_53 y_7)
	    (le_0 (Z_6 x_53) (Z_6 y_7)))))
(assert (forall ((y_7 Nat_0))
	(ge_0 y_7 Z_5)))
(assert (forall ((x_53 Nat_0) (y_7 Nat_0))
	(=> (ge_0 x_53 y_7)
	    (ge_0 (Z_6 x_53) (Z_6 y_7)))))
(assert (forall ((y_7 Nat_0))
	(lt_0 Z_5 (Z_6 y_7))))
(assert (forall ((x_53 Nat_0) (y_7 Nat_0))
	(=> (lt_0 x_53 y_7)
	    (lt_0 (Z_6 x_53) (Z_6 y_7)))))
(assert (forall ((y_7 Nat_0))
	(gt_0 (Z_6 y_7) Z_5)))
(assert (forall ((x_53 Nat_0) (y_7 Nat_0))
	(=> (gt_0 x_53 y_7)
	    (gt_0 (Z_6 x_53) (Z_6 y_7)))))
(assert (forall ((y_7 Nat_0))
	(mult_0 Z_5 Z_5 y_7)))
(assert (forall ((r_0 Nat_0) (x_53 Nat_0) (y_7 Nat_0) (z_7 Nat_0))
	(=>	(and (mult_0 r_0 x_53 y_7)
			(add_0 z_7 r_0 y_7))
		(mult_0 z_7 (Z_6 x_53) y_7))))
(assert (forall ((x_53 Nat_0) (y_7 Nat_0))
	(=> (lt_0 x_53 y_7)
	    (div_0 Z_5 x_53 y_7))))
(assert (forall ((r_0 Nat_0) (x_53 Nat_0) (y_7 Nat_0) (z_7 Nat_0))
	(=>	(and (ge_0 x_53 y_7)
			(minus_0 z_7 x_53 y_7)
			(div_0 r_0 z_7 y_7))
		(div_0 (Z_6 r_0) x_53 y_7))))
(assert (forall ((x_53 Nat_0) (y_7 Nat_0))
	(=> (lt_0 x_53 y_7)
	    (mod_0 x_53 x_53 y_7))))
(assert (forall ((r_0 Nat_0) (x_53 Nat_0) (y_7 Nat_0) (z_7 Nat_0))
	(=>	(and (ge_0 x_53 y_7)
			(minus_0 z_7 x_53 y_7)
			(mod_0 r_0 z_7 y_7))
		(mod_0 r_0 x_53 y_7))))
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
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_70 Nat_0) (x_71 list_0))
	(head_1 x_70 (cons_0 x_70 x_71))))
(assert (forall ((x_70 Nat_0) (x_71 list_0))
	(tail_1 x_71 (cons_0 x_70 x_71))))
(assert (isnil_0 nil_0))
(assert (forall ((x_73 Nat_0) (x_74 list_0))
	(iscons_0 (cons_0 x_73 x_74))))
(assert (forall ((x_75 Nat_0) (x_76 list_0))
	(diseqlist_0 nil_0 (cons_0 x_75 x_76))))
(assert (forall ((x_77 Nat_0) (x_78 list_0))
	(diseqlist_0 (cons_0 x_77 x_78) nil_0)))
(assert (forall ((x_79 Nat_0) (x_80 list_0) (x_81 Nat_0) (x_82 list_0))
	(=> (diseqNat_0 x_79 x_81)
	    (diseqlist_0 (cons_0 x_79 x_80) (cons_0 x_81 x_82)))))
(assert (forall ((x_79 Nat_0) (x_80 list_0) (x_81 Nat_0) (x_82 list_0))
	(=> (diseqlist_0 x_80 x_82)
	    (diseqlist_0 (cons_0 x_79 x_80) (cons_0 x_81 x_82)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_0 Nat_0) (y_0 list_0))
	(=> (le_0 x_0 Z_5)
	    (take_0 nil_0 x_0 y_0))))
(assert (forall ((x_54 Nat_0) (x_14 list_0) (z_0 Nat_0) (xs_0 list_0) (x_0 Nat_0))
	(=>	(and (gt_0 x_0 Z_5)
			(take_0 x_14 x_54 xs_0)
			(minus_0 x_54 x_0 (Z_6 Z_5)))
		(take_0 (cons_0 z_0 x_14) x_0 (cons_0 z_0 xs_0)))))
(assert (forall ((x_0 Nat_0) (y_0 list_0))
	(=> (le_0 x_0 Z_5)
	    (take_0 nil_0 x_0 y_0))))
(assert (forall ((x_0 Nat_0))
	(=> (gt_0 x_0 Z_5)
	    (take_0 nil_0 x_0 nil_0))))
(declare-fun ordered_0 (Bool_0 list_0) Bool)
(assert (forall ((x_17 Bool_0) (y_2 Nat_0) (xs_1 list_0) (y_1 Nat_0))
	(=>	(and (le_0 y_1 y_2)
			(ordered_0 x_17 (cons_0 y_2 xs_1)))
		(ordered_0 x_17 (cons_0 y_1 (cons_0 y_2 xs_1))))))
(assert (forall ((y_2 Nat_0) (xs_1 list_0) (y_1 Nat_0))
	(=> (gt_0 y_1 y_2)
	    (ordered_0 false_0 (cons_0 y_1 (cons_0 y_2 xs_1))))))
(assert (forall ((y_1 Nat_0))
	(ordered_0 true_0 (cons_0 y_1 nil_0))))
(assert (ordered_0 true_0 nil_0))
(declare-fun nmsorttdhalf_0 (Nat_0 Nat_0) Bool)
(assert (nmsorttdhalf_0 Z_5 (Z_6 Z_5)))
(assert (=> (diseqNat_0 Z_5 (Z_6 Z_5))
	    (nmsorttdhalf_0 Z_5 Z_5)))
(assert (nmsorttdhalf_0 Z_5 (Z_6 Z_5)))
(assert (forall ((x_56 Nat_0) (x_25 Nat_0) (x_26 Nat_0) (x_2 Nat_0))
	(=>	(and (diseqNat_0 x_2 (Z_6 Z_5))
			(diseqNat_0 x_2 Z_5)
			(nmsorttdhalf_0 x_26 x_56)
			(minus_0 x_56 x_2 (Z_6 (Z_6 Z_5)))
			(add_0 x_25 (Z_6 Z_5) x_26))
		(nmsorttdhalf_0 x_25 x_2))))
(declare-fun lmerge_0 (list_0 list_0 list_0) Bool)
(assert (forall ((x_28 list_0) (x_5 Nat_0) (x_6 list_0) (z_2 Nat_0) (x_4 list_0))
	(=>	(and (le_0 z_2 x_5)
			(lmerge_0 x_28 x_4 (cons_0 x_5 x_6)))
		(lmerge_0 (cons_0 z_2 x_28) (cons_0 z_2 x_4) (cons_0 x_5 x_6)))))
(assert (forall ((x_30 list_0) (x_5 Nat_0) (x_6 list_0) (z_2 Nat_0) (x_4 list_0))
	(=>	(and (gt_0 z_2 x_5)
			(lmerge_0 x_30 (cons_0 z_2 x_4) x_6))
		(lmerge_0 (cons_0 x_5 x_30) (cons_0 z_2 x_4) (cons_0 x_5 x_6)))))
(assert (forall ((z_2 Nat_0) (x_4 list_0))
	(lmerge_0 (cons_0 z_2 x_4) (cons_0 z_2 x_4) nil_0)))
(assert (forall ((x_32 list_0))
	(lmerge_0 x_32 nil_0 x_32)))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_33 Nat_0) (x_34 Nat_0) (y_4 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_34 l_0)
			(add_0 x_33 (Z_6 Z_5) x_34))
		(length_0 x_33 (cons_0 y_4 l_0)))))
(assert (length_0 Z_5 nil_0))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_36 list_0) (x_8 Nat_0))
	(=> (le_0 x_8 Z_5)
	    (drop_0 x_36 x_8 x_36))))
(assert (forall ((x_58 Nat_0) (x_37 list_0) (z_3 Nat_0) (xs_2 list_0) (x_8 Nat_0))
	(=>	(and (gt_0 x_8 Z_5)
			(drop_0 x_37 x_58 xs_2)
			(minus_0 x_58 x_8 (Z_6 Z_5)))
		(drop_0 x_37 x_8 (cons_0 z_3 xs_2)))))
(assert (forall ((x_39 list_0) (x_8 Nat_0))
	(=> (le_0 x_8 Z_5)
	    (drop_0 x_39 x_8 x_39))))
(assert (forall ((x_8 Nat_0))
	(=> (gt_0 x_8 Z_5)
	    (drop_0 nil_0 x_8 nil_0))))
(declare-fun nmsorttd_0 (list_0 list_0) Bool)
(assert (forall ((x_43 list_0) (x_44 list_0) (x_45 list_0) (x_46 list_0) (x_47 list_0) (x_41 Nat_0) (k_0 Nat_0) (x_10 Nat_0) (x_11 list_0) (y_6 Nat_0))
	(=>	(and (take_0 x_44 k_0 (cons_0 y_6 (cons_0 x_10 x_11)))
			(nmsorttd_0 x_45 x_44)
			(drop_0 x_46 k_0 (cons_0 y_6 (cons_0 x_10 x_11)))
			(nmsorttd_0 x_47 x_46)
			(lmerge_0 x_43 x_45 x_47)
			(length_0 x_41 (cons_0 y_6 (cons_0 x_10 x_11)))
			(nmsorttdhalf_0 k_0 x_41))
		(nmsorttd_0 x_43 (cons_0 y_6 (cons_0 x_10 x_11))))))
(assert (forall ((y_6 Nat_0))
	(nmsorttd_0 (cons_0 y_6 nil_0) (cons_0 y_6 nil_0))))
(assert (nmsorttd_0 nil_0 nil_0))
(assert (forall ((x_51 list_0) (x_52 Bool_0) (xs_3 list_0))
	(=>	(and (diseqBool_0 x_52 true_0)
			(nmsorttd_0 x_51 xs_3)
			(ordered_0 x_52 x_51))
		false)))
(check-sat)
