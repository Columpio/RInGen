(set-logic HORN)
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
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_1 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_34 Nat_0))
	(p_1 x_34 (succ_0 x_34))))
(assert (iszero_0 zero_0))
(assert (forall ((x_36 Nat_0))
	(issucc_0 (succ_0 x_36))))
(assert (forall ((x_37 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_37))))
(assert (forall ((x_38 Nat_0))
	(diseqNat_0 (succ_0 x_38) zero_0)))
(assert (forall ((x_39 Nat_0) (x_40 Nat_0))
	(=> (diseqNat_0 x_39 x_40)
	    (diseqNat_0 (succ_0 x_39) (succ_0 x_40)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_42 Nat_0) (x_43 list_0))
	(head_1 x_42 (cons_0 x_42 x_43))))
(assert (forall ((x_42 Nat_0) (x_43 list_0))
	(tail_1 x_43 (cons_0 x_42 x_43))))
(assert (isnil_0 nil_0))
(assert (forall ((x_45 Nat_0) (x_46 list_0))
	(iscons_0 (cons_0 x_45 x_46))))
(assert (forall ((x_47 Nat_0) (x_48 list_0))
	(diseqlist_0 nil_0 (cons_0 x_47 x_48))))
(assert (forall ((x_49 Nat_0) (x_50 list_0))
	(diseqlist_0 (cons_0 x_49 x_50) nil_0)))
(assert (forall ((x_51 Nat_0) (x_52 list_0) (x_53 Nat_0) (x_54 list_0))
	(=> (diseqNat_0 x_51 x_53)
	    (diseqlist_0 (cons_0 x_51 x_52) (cons_0 x_53 x_54)))))
(assert (forall ((x_51 Nat_0) (x_52 list_0) (x_53 Nat_0) (x_54 list_0))
	(=> (diseqlist_0 x_52 x_54)
	    (diseqlist_0 (cons_0 x_51 x_52) (cons_0 x_53 x_54)))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 Bool_0) (projpair_1 list_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (Bool_0 pair_0) Bool)
(declare-fun projpair_3 (list_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_55 Bool_0) (x_56 list_0))
	(projpair_2 x_55 (pair_1 x_55 x_56))))
(assert (forall ((x_55 Bool_0) (x_56 list_0))
	(projpair_3 x_56 (pair_1 x_55 x_56))))
(assert (forall ((x_58 Bool_0) (x_59 list_0))
	(ispair_0 (pair_1 x_58 x_59))))
(assert (forall ((x_60 Bool_0) (x_61 list_0) (x_62 Bool_0) (x_63 list_0))
	(=> (diseqBool_0 x_60 x_62)
	    (diseqpair_0 (pair_1 x_60 x_61) (pair_1 x_62 x_63)))))
(assert (forall ((x_60 Bool_0) (x_61 list_0) (x_62 Bool_0) (x_63 list_0))
	(=> (diseqlist_0 x_61 x_63)
	    (diseqpair_0 (pair_1 x_60 x_61) (pair_1 x_62 x_63)))))
(declare-fun leq_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_5 Bool_0) (x_1 Nat_0) (z_0 Nat_0))
	(=> (leq_0 x_5 z_0 x_1)
	    (leq_0 x_5 (succ_0 z_0) (succ_0 x_1)))))
(assert (forall ((z_0 Nat_0))
	(leq_0 false_0 (succ_0 z_0) zero_0)))
(assert (forall ((y_0 Nat_0))
	(leq_0 true_0 zero_0 y_0)))
(declare-fun ordered_0 (Bool_0 list_0) Bool)
(assert (forall ((x_29 Bool_0) (x_10 Bool_0) (x_11 Bool_0) (y_2 Nat_0) (xs_0 list_0) (y_1 Nat_0))
	(=>	(and (leq_0 x_10 y_1 y_2)
			(ordered_0 x_11 (cons_0 y_2 xs_0))
			(and_0 x_29 x_10 x_11))
		(ordered_0 x_29 (cons_0 y_1 (cons_0 y_2 xs_0))))))
(assert (forall ((y_1 Nat_0))
	(ordered_0 true_0 (cons_0 y_1 nil_0))))
(assert (ordered_0 true_0 nil_0))
(declare-fun bubble_0 (pair_0 list_0) Bool)
(assert (forall ((b_0 Bool_0) (ys_0 list_0) (y_4 Nat_0) (xs_1 list_0) (y_3 Nat_0))
	(=>	(and (bubble_0 (pair_1 b_0 ys_0) (cons_0 y_4 xs_1))
			(leq_0 true_0 y_3 y_4))
		(bubble_0 (pair_1 b_0 (cons_0 y_3 ys_0)) (cons_0 y_3 (cons_0 y_4 xs_1))))))
(assert (forall ((x_17 Bool_0) (b_1 Bool_0) (ys_1 list_0) (y_4 Nat_0) (xs_1 list_0) (y_3 Nat_0))
	(=>	(and (diseqBool_0 x_17 true_0)
			(bubble_0 (pair_1 b_1 ys_1) (cons_0 y_3 xs_1))
			(leq_0 x_17 y_3 y_4))
		(bubble_0 (pair_1 true_0 (cons_0 y_4 ys_1)) (cons_0 y_3 (cons_0 y_4 xs_1))))))
(assert (forall ((y_3 Nat_0))
	(bubble_0 (pair_1 false_0 (cons_0 y_3 nil_0)) (cons_0 y_3 nil_0))))
(assert (bubble_0 (pair_1 false_0 nil_0) nil_0))
(declare-fun bubsort_0 (list_0 list_0) Bool)
(assert (forall ((x_23 list_0) (ys_2 list_0) (x_4 list_0))
	(=>	(and (bubsort_0 x_23 ys_2)
			(bubble_0 (pair_1 true_0 ys_2) x_4))
		(bubsort_0 x_23 x_4))))
(assert (forall ((x_26 list_0) (c_0 Bool_0) (ys_2 list_0))
	(=>	(and (diseqBool_0 c_0 true_0)
			(bubble_0 (pair_1 c_0 ys_2) x_26))
		(bubsort_0 x_26 x_26))))
(assert (forall ((x_27 list_0) (x_28 Bool_0) (xs_2 list_0))
	(=>	(and (diseqBool_0 x_28 true_0)
			(bubsort_0 x_27 xs_2)
			(ordered_0 x_28 x_27))
		false)))
(check-sat)
