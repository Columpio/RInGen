(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_2 ) (Z_3 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_20 Nat_0))
	(unS_1 x_20 (Z_3 x_20))))
(assert (isZ_2 Z_2))
(assert (forall ((x_22 Nat_0))
	(isZ_3 (Z_3 x_22))))
(assert (forall ((x_23 Nat_0))
	(diseqNat_0 Z_2 (Z_3 x_23))))
(assert (forall ((x_24 Nat_0))
	(diseqNat_0 (Z_3 x_24) Z_2)))
(assert (forall ((x_25 Nat_0) (x_26 Nat_0))
	(=> (diseqNat_0 x_25 x_26)
	    (diseqNat_0 (Z_3 x_25) (Z_3 x_26)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_5 Nat_0))
	(add_0 y_5 Z_2 y_5)))
(assert (forall ((r_0 Nat_0) (x_16 Nat_0) (y_5 Nat_0))
	(=> (add_0 r_0 x_16 y_5)
	    (add_0 (Z_3 r_0) (Z_3 x_16) y_5))))
(assert (forall ((y_5 Nat_0))
	(minus_0 Z_2 Z_2 y_5)))
(assert (forall ((r_0 Nat_0) (x_16 Nat_0) (y_5 Nat_0))
	(=> (minus_0 r_0 x_16 y_5)
	    (minus_0 (Z_3 r_0) (Z_3 x_16) y_5))))
(assert (forall ((y_5 Nat_0))
	(le_0 Z_2 y_5)))
(assert (forall ((x_16 Nat_0) (y_5 Nat_0))
	(=> (le_0 x_16 y_5)
	    (le_0 (Z_3 x_16) (Z_3 y_5)))))
(assert (forall ((y_5 Nat_0))
	(ge_0 y_5 Z_2)))
(assert (forall ((x_16 Nat_0) (y_5 Nat_0))
	(=> (ge_0 x_16 y_5)
	    (ge_0 (Z_3 x_16) (Z_3 y_5)))))
(assert (forall ((y_5 Nat_0))
	(lt_0 Z_2 (Z_3 y_5))))
(assert (forall ((x_16 Nat_0) (y_5 Nat_0))
	(=> (lt_0 x_16 y_5)
	    (lt_0 (Z_3 x_16) (Z_3 y_5)))))
(assert (forall ((y_5 Nat_0))
	(gt_0 (Z_3 y_5) Z_2)))
(assert (forall ((x_16 Nat_0) (y_5 Nat_0))
	(=> (gt_0 x_16 y_5)
	    (gt_0 (Z_3 x_16) (Z_3 y_5)))))
(assert (forall ((y_5 Nat_0))
	(mult_0 Z_2 Z_2 y_5)))
(assert (forall ((r_0 Nat_0) (x_16 Nat_0) (y_5 Nat_0) (z_4 Nat_0))
	(=>	(and (mult_0 r_0 x_16 y_5)
			(add_0 z_4 r_0 y_5))
		(mult_0 z_4 (Z_3 x_16) y_5))))
(assert (forall ((x_16 Nat_0) (y_5 Nat_0))
	(=> (lt_0 x_16 y_5)
	    (div_0 Z_2 x_16 y_5))))
(assert (forall ((r_0 Nat_0) (x_16 Nat_0) (y_5 Nat_0) (z_4 Nat_0))
	(=>	(and (ge_0 x_16 y_5)
			(minus_0 z_4 x_16 y_5)
			(div_0 r_0 z_4 y_5))
		(div_0 (Z_3 r_0) x_16 y_5))))
(assert (forall ((x_16 Nat_0) (y_5 Nat_0))
	(=> (lt_0 x_16 y_5)
	    (mod_0 x_16 x_16 y_5))))
(assert (forall ((r_0 Nat_0) (x_16 Nat_0) (y_5 Nat_0) (z_4 Nat_0))
	(=>	(and (ge_0 x_16 y_5)
			(minus_0 z_4 x_16 y_5)
			(mod_0 r_0 z_4 y_5))
		(mod_0 r_0 x_16 y_5))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 Nat_0) (projpair_1 Nat_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (Nat_0 pair_0) Bool)
(declare-fun projpair_3 (Nat_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_27 Nat_0) (x_28 Nat_0))
	(projpair_2 x_27 (pair_1 x_27 x_28))))
(assert (forall ((x_27 Nat_0) (x_28 Nat_0))
	(projpair_3 x_28 (pair_1 x_27 x_28))))
(assert (forall ((x_30 Nat_0) (x_31 Nat_0))
	(ispair_0 (pair_1 x_30 x_31))))
(assert (forall ((x_32 Nat_0) (x_33 Nat_0) (x_34 Nat_0) (x_35 Nat_0))
	(=> (diseqNat_0 x_32 x_34)
	    (diseqpair_0 (pair_1 x_32 x_33) (pair_1 x_34 x_35)))))
(assert (forall ((x_32 Nat_0) (x_33 Nat_0) (x_34 Nat_0) (x_35 Nat_0))
	(=> (diseqNat_0 x_33 x_35)
	    (diseqpair_0 (pair_1 x_32 x_33) (pair_1 x_34 x_35)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_2 (Nat_0 list_0) Bool)
(declare-fun tail_2 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_37 Nat_0) (x_38 list_0))
	(head_2 x_37 (cons_0 x_37 x_38))))
(assert (forall ((x_37 Nat_0) (x_38 list_0))
	(tail_2 x_38 (cons_0 x_37 x_38))))
(assert (isnil_0 nil_0))
(assert (forall ((x_40 Nat_0) (x_41 list_0))
	(iscons_0 (cons_0 x_40 x_41))))
(assert (forall ((x_42 Nat_0) (x_43 list_0))
	(diseqlist_0 nil_0 (cons_0 x_42 x_43))))
(assert (forall ((x_44 Nat_0) (x_45 list_0))
	(diseqlist_0 (cons_0 x_44 x_45) nil_0)))
(assert (forall ((x_46 Nat_0) (x_47 list_0) (x_48 Nat_0) (x_49 list_0))
	(=> (diseqNat_0 x_46 x_48)
	    (diseqlist_0 (cons_0 x_46 x_47) (cons_0 x_48 x_49)))))
(assert (forall ((x_46 Nat_0) (x_47 list_0) (x_48 Nat_0) (x_49 list_0))
	(=> (diseqlist_0 x_47 x_49)
	    (diseqlist_0 (cons_0 x_46 x_47) (cons_0 x_48 x_49)))))
(declare-datatypes ((list_1 0)) (((nil_1 ) (cons_1 (head_1 pair_0) (tail_1 list_1)))))
(declare-fun diseqlist_1 (list_1 list_1) Bool)
(declare-fun head_3 (pair_0 list_1) Bool)
(declare-fun tail_3 (list_1 list_1) Bool)
(declare-fun isnil_1 (list_1) Bool)
(declare-fun iscons_1 (list_1) Bool)
(assert (forall ((x_51 pair_0) (x_52 list_1))
	(head_3 x_51 (cons_1 x_51 x_52))))
(assert (forall ((x_51 pair_0) (x_52 list_1))
	(tail_3 x_52 (cons_1 x_51 x_52))))
(assert (isnil_1 nil_1))
(assert (forall ((x_54 pair_0) (x_55 list_1))
	(iscons_1 (cons_1 x_54 x_55))))
(assert (forall ((x_56 pair_0) (x_57 list_1))
	(diseqlist_1 nil_1 (cons_1 x_56 x_57))))
(assert (forall ((x_58 pair_0) (x_59 list_1))
	(diseqlist_1 (cons_1 x_58 x_59) nil_1)))
(assert (forall ((x_60 pair_0) (x_61 list_1) (x_62 pair_0) (x_63 list_1))
	(=> (diseqpair_0 x_60 x_62)
	    (diseqlist_1 (cons_1 x_60 x_61) (cons_1 x_62 x_63)))))
(assert (forall ((x_60 pair_0) (x_61 list_1) (x_62 pair_0) (x_63 list_1))
	(=> (diseqlist_1 x_61 x_63)
	    (diseqlist_1 (cons_1 x_60 x_61) (cons_1 x_62 x_63)))))
(declare-fun unpair_0 (list_0 list_1) Bool)
(assert (forall ((x_4 list_0) (z_0 Nat_0) (y_1 Nat_0) (xys_0 list_1))
	(=> (unpair_0 x_4 xys_0)
	    (unpair_0 (cons_0 z_0 (cons_0 y_1 x_4)) (cons_1 (pair_1 z_0 y_1) xys_0)))))
(assert (unpair_0 nil_0 nil_1))
(declare-fun pairs_0 (list_1 list_0) Bool)
(assert (forall ((x_7 list_1) (y_3 Nat_0) (xs_0 list_0) (y_2 Nat_0))
	(=> (pairs_0 x_7 xs_0)
	    (pairs_0 (cons_1 (pair_1 y_2 y_3) x_7) (cons_0 y_2 (cons_0 y_3 xs_0))))))
(assert (forall ((y_2 Nat_0))
	(pairs_0 nil_1 (cons_0 y_2 nil_0))))
(assert (pairs_0 nil_1 nil_0))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_10 Nat_0) (x_11 Nat_0) (y_4 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_11 l_0)
			(add_0 x_10 (Z_3 Z_2) x_11))
		(length_0 x_10 (cons_0 y_4 l_0)))))
(assert (length_0 Z_2 nil_0))
(assert (forall ((x_15 Nat_0) (x_13 list_1) (x_14 list_0) (xs_1 list_0))
	(=>	(and (diseqlist_0 x_14 xs_1)
			(length_0 x_15 xs_1)
			(pairs_0 x_13 xs_1)
			(unpair_0 x_14 x_13)
			(mod_0 Z_2 x_15 (Z_3 (Z_3 Z_2))))
		false)))
(check-sat)