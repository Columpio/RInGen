(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_2 ) (Z_3 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_23 Nat_0))
	(unS_1 x_23 (Z_3 x_23))))
(assert (isZ_2 Z_2))
(assert (forall ((x_25 Nat_0))
	(isZ_3 (Z_3 x_25))))
(assert (forall ((x_26 Nat_0))
	(diseqNat_0 Z_2 (Z_3 x_26))))
(assert (forall ((x_27 Nat_0))
	(diseqNat_0 (Z_3 x_27) Z_2)))
(assert (forall ((x_28 Nat_0) (x_29 Nat_0))
	(=> (diseqNat_0 x_28 x_29)
	    (diseqNat_0 (Z_3 x_28) (Z_3 x_29)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_4 Nat_0))
	(add_0 y_4 Z_2 y_4)))
(assert (forall ((r_0 Nat_0) (x_21 Nat_0) (y_4 Nat_0))
	(=> (add_0 r_0 x_21 y_4)
	    (add_0 (Z_3 r_0) (Z_3 x_21) y_4))))
(assert (forall ((y_4 Nat_0))
	(minus_0 Z_2 Z_2 y_4)))
(assert (forall ((r_0 Nat_0) (x_21 Nat_0) (y_4 Nat_0))
	(=> (minus_0 r_0 x_21 y_4)
	    (minus_0 (Z_3 r_0) (Z_3 x_21) y_4))))
(assert (forall ((y_4 Nat_0))
	(le_0 Z_2 y_4)))
(assert (forall ((x_21 Nat_0) (y_4 Nat_0))
	(=> (le_0 x_21 y_4)
	    (le_0 (Z_3 x_21) (Z_3 y_4)))))
(assert (forall ((y_4 Nat_0))
	(ge_0 y_4 Z_2)))
(assert (forall ((x_21 Nat_0) (y_4 Nat_0))
	(=> (ge_0 x_21 y_4)
	    (ge_0 (Z_3 x_21) (Z_3 y_4)))))
(assert (forall ((y_4 Nat_0))
	(lt_0 Z_2 (Z_3 y_4))))
(assert (forall ((x_21 Nat_0) (y_4 Nat_0))
	(=> (lt_0 x_21 y_4)
	    (lt_0 (Z_3 x_21) (Z_3 y_4)))))
(assert (forall ((y_4 Nat_0))
	(gt_0 (Z_3 y_4) Z_2)))
(assert (forall ((x_21 Nat_0) (y_4 Nat_0))
	(=> (gt_0 x_21 y_4)
	    (gt_0 (Z_3 x_21) (Z_3 y_4)))))
(assert (forall ((y_4 Nat_0))
	(mult_0 Z_2 Z_2 y_4)))
(assert (forall ((r_0 Nat_0) (x_21 Nat_0) (y_4 Nat_0) (z_4 Nat_0))
	(=>	(and (mult_0 r_0 x_21 y_4)
			(add_0 z_4 r_0 y_4))
		(mult_0 z_4 (Z_3 x_21) y_4))))
(assert (forall ((x_21 Nat_0) (y_4 Nat_0))
	(=> (lt_0 x_21 y_4)
	    (div_0 Z_2 x_21 y_4))))
(assert (forall ((r_0 Nat_0) (x_21 Nat_0) (y_4 Nat_0) (z_4 Nat_0))
	(=>	(and (ge_0 x_21 y_4)
			(minus_0 z_4 x_21 y_4)
			(div_0 r_0 z_4 y_4))
		(div_0 (Z_3 r_0) x_21 y_4))))
(assert (forall ((x_21 Nat_0) (y_4 Nat_0))
	(=> (lt_0 x_21 y_4)
	    (mod_0 x_21 x_21 y_4))))
(assert (forall ((r_0 Nat_0) (x_21 Nat_0) (y_4 Nat_0) (z_4 Nat_0))
	(=>	(and (ge_0 x_21 y_4)
			(minus_0 z_4 x_21 y_4)
			(mod_0 r_0 z_4 y_4))
		(mod_0 r_0 x_21 y_4))))
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
(assert (forall ((x_33 Nat_0) (x_34 list_0))
	(head_1 x_33 (cons_0 x_33 x_34))))
(assert (forall ((x_33 Nat_0) (x_34 list_0))
	(tail_1 x_34 (cons_0 x_33 x_34))))
(assert (isnil_0 nil_0))
(assert (forall ((x_36 Nat_0) (x_37 list_0))
	(iscons_0 (cons_0 x_36 x_37))))
(assert (forall ((x_38 Nat_0) (x_39 list_0))
	(diseqlist_0 nil_0 (cons_0 x_38 x_39))))
(assert (forall ((x_40 Nat_0) (x_41 list_0))
	(diseqlist_0 (cons_0 x_40 x_41) nil_0)))
(assert (forall ((x_42 Nat_0) (x_43 list_0) (x_44 Nat_0) (x_45 list_0))
	(=> (diseqNat_0 x_42 x_44)
	    (diseqlist_0 (cons_0 x_42 x_43) (cons_0 x_44 x_45)))))
(assert (forall ((x_42 Nat_0) (x_43 list_0) (x_44 Nat_0) (x_45 list_0))
	(=> (diseqlist_0 x_43 x_45)
	    (diseqlist_0 (cons_0 x_42 x_43) (cons_0 x_44 x_45)))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 Bool_0) (projpair_1 list_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (Bool_0 pair_0) Bool)
(declare-fun projpair_3 (list_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_46 Bool_0) (x_47 list_0))
	(projpair_2 x_46 (pair_1 x_46 x_47))))
(assert (forall ((x_46 Bool_0) (x_47 list_0))
	(projpair_3 x_47 (pair_1 x_46 x_47))))
(assert (forall ((x_49 Bool_0) (x_50 list_0))
	(ispair_0 (pair_1 x_49 x_50))))
(assert (forall ((x_51 Bool_0) (x_52 list_0) (x_53 Bool_0) (x_54 list_0))
	(=> (diseqBool_0 x_51 x_53)
	    (diseqpair_0 (pair_1 x_51 x_52) (pair_1 x_53 x_54)))))
(assert (forall ((x_51 Bool_0) (x_52 list_0) (x_53 Bool_0) (x_54 list_0))
	(=> (diseqlist_0 x_52 x_54)
	    (diseqpair_0 (pair_1 x_51 x_52) (pair_1 x_53 x_54)))))
(declare-fun ordered_0 (Bool_0 list_0) Bool)
(assert (forall ((x_3 Bool_0) (y_1 Nat_0) (xs_0 list_0) (y_0 Nat_0))
	(=>	(and (le_0 y_0 y_1)
			(ordered_0 x_3 (cons_0 y_1 xs_0)))
		(ordered_0 x_3 (cons_0 y_0 (cons_0 y_1 xs_0))))))
(assert (forall ((y_1 Nat_0) (xs_0 list_0) (y_0 Nat_0))
	(=> (gt_0 y_0 y_1)
	    (ordered_0 false_0 (cons_0 y_0 (cons_0 y_1 xs_0))))))
(assert (forall ((y_0 Nat_0))
	(ordered_0 true_0 (cons_0 y_0 nil_0))))
(assert (ordered_0 true_0 nil_0))
(declare-fun bubble_0 (pair_0 list_0) Bool)
(assert (forall ((b_0 Bool_0) (ys_0 list_0) (y_3 Nat_0) (xs_1 list_0) (y_2 Nat_0))
	(=>	(and (le_0 y_2 y_3)
			(bubble_0 (pair_1 b_0 ys_0) (cons_0 y_3 xs_1)))
		(bubble_0 (pair_1 b_0 (cons_0 y_2 ys_0)) (cons_0 y_2 (cons_0 y_3 xs_1))))))
(assert (forall ((b_1 Bool_0) (ys_1 list_0) (y_3 Nat_0) (xs_1 list_0) (y_2 Nat_0))
	(=>	(and (gt_0 y_2 y_3)
			(bubble_0 (pair_1 b_1 ys_1) (cons_0 y_2 xs_1)))
		(bubble_0 (pair_1 true_0 (cons_0 y_3 ys_1)) (cons_0 y_2 (cons_0 y_3 xs_1))))))
(assert (forall ((y_2 Nat_0))
	(bubble_0 (pair_1 false_0 (cons_0 y_2 nil_0)) (cons_0 y_2 nil_0))))
(assert (bubble_0 (pair_1 false_0 nil_0) nil_0))
(declare-fun bubsort_0 (list_0 list_0) Bool)
(assert (forall ((x_15 list_0) (ys_2 list_0) (x_2 list_0))
	(=>	(and (bubsort_0 x_15 ys_2)
			(bubble_0 (pair_1 true_0 ys_2) x_2))
		(bubsort_0 x_15 x_2))))
(assert (forall ((x_18 list_0) (c_0 Bool_0) (ys_2 list_0))
	(=>	(and (diseqBool_0 c_0 true_0)
			(bubble_0 (pair_1 c_0 ys_2) x_18))
		(bubsort_0 x_18 x_18))))
(assert (forall ((x_19 list_0) (x_20 Bool_0) (xs_2 list_0))
	(=>	(and (diseqBool_0 x_20 true_0)
			(bubsort_0 x_19 xs_2)
			(ordered_0 x_20 x_19))
		false)))
(check-sat)