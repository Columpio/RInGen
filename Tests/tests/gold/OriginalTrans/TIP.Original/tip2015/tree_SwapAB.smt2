(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_3 ) (Z_4 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_48 Nat_0))
	(unS_1 x_48 (Z_4 x_48))))
(assert (isZ_2 Z_3))
(assert (forall ((x_50 Nat_0))
	(isZ_3 (Z_4 x_50))))
(assert (forall ((x_51 Nat_0))
	(diseqNat_0 Z_3 (Z_4 x_51))))
(assert (forall ((x_52 Nat_0))
	(diseqNat_0 (Z_4 x_52) Z_3)))
(assert (forall ((x_53 Nat_0) (x_54 Nat_0))
	(=> (diseqNat_0 x_53 x_54)
	    (diseqNat_0 (Z_4 x_53) (Z_4 x_54)))))
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
	(add_0 y_4 Z_3 y_4)))
(assert (forall ((r_0 Nat_0) (x_46 Nat_0) (y_4 Nat_0))
	(=> (add_0 r_0 x_46 y_4)
	    (add_0 (Z_4 r_0) (Z_4 x_46) y_4))))
(assert (forall ((y_4 Nat_0))
	(minus_0 Z_3 Z_3 y_4)))
(assert (forall ((r_0 Nat_0) (x_46 Nat_0) (y_4 Nat_0))
	(=> (minus_0 r_0 x_46 y_4)
	    (minus_0 (Z_4 r_0) (Z_4 x_46) y_4))))
(assert (forall ((y_4 Nat_0))
	(le_0 Z_3 y_4)))
(assert (forall ((x_46 Nat_0) (y_4 Nat_0))
	(=> (le_0 x_46 y_4)
	    (le_0 (Z_4 x_46) (Z_4 y_4)))))
(assert (forall ((y_4 Nat_0))
	(ge_0 y_4 Z_3)))
(assert (forall ((x_46 Nat_0) (y_4 Nat_0))
	(=> (ge_0 x_46 y_4)
	    (ge_0 (Z_4 x_46) (Z_4 y_4)))))
(assert (forall ((y_4 Nat_0))
	(lt_0 Z_3 (Z_4 y_4))))
(assert (forall ((x_46 Nat_0) (y_4 Nat_0))
	(=> (lt_0 x_46 y_4)
	    (lt_0 (Z_4 x_46) (Z_4 y_4)))))
(assert (forall ((y_4 Nat_0))
	(gt_0 (Z_4 y_4) Z_3)))
(assert (forall ((x_46 Nat_0) (y_4 Nat_0))
	(=> (gt_0 x_46 y_4)
	    (gt_0 (Z_4 x_46) (Z_4 y_4)))))
(assert (forall ((y_4 Nat_0))
	(mult_0 Z_3 Z_3 y_4)))
(assert (forall ((r_0 Nat_0) (x_46 Nat_0) (y_4 Nat_0) (z_5 Nat_0))
	(=>	(and (mult_0 r_0 x_46 y_4)
			(add_0 z_5 r_0 y_4))
		(mult_0 z_5 (Z_4 x_46) y_4))))
(assert (forall ((x_46 Nat_0) (y_4 Nat_0))
	(=> (lt_0 x_46 y_4)
	    (div_0 Z_3 x_46 y_4))))
(assert (forall ((r_0 Nat_0) (x_46 Nat_0) (y_4 Nat_0) (z_5 Nat_0))
	(=>	(and (ge_0 x_46 y_4)
			(minus_0 z_5 x_46 y_4)
			(div_0 r_0 z_5 y_4))
		(div_0 (Z_4 r_0) x_46 y_4))))
(assert (forall ((x_46 Nat_0) (y_4 Nat_0))
	(=> (lt_0 x_46 y_4)
	    (mod_0 x_46 x_46 y_4))))
(assert (forall ((r_0 Nat_0) (x_46 Nat_0) (y_4 Nat_0) (z_5 Nat_0))
	(=>	(and (ge_0 x_46 y_4)
			(minus_0 z_5 x_46 y_4)
			(mod_0 r_0 z_5 y_4))
		(mod_0 r_0 x_46 y_4))))
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
(assert (forall ((x_58 Nat_0) (x_59 list_0))
	(head_1 x_58 (cons_0 x_58 x_59))))
(assert (forall ((x_58 Nat_0) (x_59 list_0))
	(tail_1 x_59 (cons_0 x_58 x_59))))
(assert (isnil_0 nil_0))
(assert (forall ((x_61 Nat_0) (x_62 list_0))
	(iscons_0 (cons_0 x_61 x_62))))
(assert (forall ((x_63 Nat_0) (x_64 list_0))
	(diseqlist_0 nil_0 (cons_0 x_63 x_64))))
(assert (forall ((x_65 Nat_0) (x_66 list_0))
	(diseqlist_0 (cons_0 x_65 x_66) nil_0)))
(assert (forall ((x_67 Nat_0) (x_68 list_0) (x_69 Nat_0) (x_70 list_0))
	(=> (diseqNat_0 x_67 x_69)
	    (diseqlist_0 (cons_0 x_67 x_68) (cons_0 x_69 x_70)))))
(assert (forall ((x_67 Nat_0) (x_68 list_0) (x_69 Nat_0) (x_70 list_0))
	(=> (diseqlist_0 x_68 x_70)
	    (diseqlist_0 (cons_0 x_67 x_68) (cons_0 x_69 x_70)))))
(declare-datatypes ((Tree_0 0)) (((Node_0 (projNode_0 Tree_0) (projNode_1 Nat_0) (projNode_2 Tree_0)) (Nil_1 ))))
(declare-fun diseqTree_0 (Tree_0 Tree_0) Bool)
(declare-fun projNode_3 (Tree_0 Tree_0) Bool)
(declare-fun projNode_4 (Nat_0 Tree_0) Bool)
(declare-fun projNode_5 (Tree_0 Tree_0) Bool)
(declare-fun isNode_0 (Tree_0) Bool)
(declare-fun isNil_1 (Tree_0) Bool)
(assert (forall ((x_71 Tree_0) (x_72 Nat_0) (x_73 Tree_0))
	(projNode_3 x_71 (Node_0 x_71 x_72 x_73))))
(assert (forall ((x_71 Tree_0) (x_72 Nat_0) (x_73 Tree_0))
	(projNode_4 x_72 (Node_0 x_71 x_72 x_73))))
(assert (forall ((x_71 Tree_0) (x_72 Nat_0) (x_73 Tree_0))
	(projNode_5 x_73 (Node_0 x_71 x_72 x_73))))
(assert (forall ((x_76 Tree_0) (x_77 Nat_0) (x_78 Tree_0))
	(isNode_0 (Node_0 x_76 x_77 x_78))))
(assert (isNil_1 Nil_1))
(assert (forall ((x_79 Tree_0) (x_80 Nat_0) (x_81 Tree_0))
	(diseqTree_0 (Node_0 x_79 x_80 x_81) Nil_1)))
(assert (forall ((x_82 Tree_0) (x_83 Nat_0) (x_84 Tree_0))
	(diseqTree_0 Nil_1 (Node_0 x_82 x_83 x_84))))
(assert (forall ((x_85 Tree_0) (x_86 Nat_0) (x_87 Tree_0) (x_88 Tree_0) (x_89 Nat_0) (x_90 Tree_0))
	(=> (diseqTree_0 x_85 x_88)
	    (diseqTree_0 (Node_0 x_85 x_86 x_87) (Node_0 x_88 x_89 x_90)))))
(assert (forall ((x_85 Tree_0) (x_86 Nat_0) (x_87 Tree_0) (x_88 Tree_0) (x_89 Nat_0) (x_90 Tree_0))
	(=> (diseqNat_0 x_86 x_89)
	    (diseqTree_0 (Node_0 x_85 x_86 x_87) (Node_0 x_88 x_89 x_90)))))
(assert (forall ((x_85 Tree_0) (x_86 Nat_0) (x_87 Tree_0) (x_88 Tree_0) (x_89 Nat_0) (x_90 Tree_0))
	(=> (diseqTree_0 x_87 x_90)
	    (diseqTree_0 (Node_0 x_85 x_86 x_87) (Node_0 x_88 x_89 x_90)))))
(declare-fun swap_0 (Tree_0 Nat_0 Nat_0 Tree_0) Bool)
(assert (forall ((x_0 Nat_0) (y_0 Nat_0))
	(swap_0 Nil_1 x_0 y_0 Nil_1)))
(assert (forall ((x_8 Tree_0) (x_9 Tree_0) (p_0 Tree_0) (q_0 Tree_0) (x_0 Nat_0) (y_0 Nat_0))
	(=>	(and (swap_0 x_8 x_0 y_0 p_0)
			(swap_0 x_9 x_0 y_0 q_0))
		(swap_0 (Node_0 x_8 y_0 x_9) x_0 y_0 (Node_0 p_0 x_0 q_0)))))
(assert (forall ((x_11 Tree_0) (x_12 Tree_0) (p_0 Tree_0) (x_1 Nat_0) (q_0 Tree_0) (x_0 Nat_0))
	(=>	(and (diseqNat_0 x_1 x_0)
			(swap_0 x_11 x_0 x_1 p_0)
			(swap_0 x_12 x_0 x_1 q_0))
		(swap_0 (Node_0 x_11 x_0 x_12) x_0 x_1 (Node_0 p_0 x_1 q_0)))))
(assert (forall ((x_14 Tree_0) (x_15 Tree_0) (p_0 Tree_0) (q_0 Tree_0) (x_0 Nat_0) (y_0 Nat_0))
	(=>	(and (swap_0 x_14 x_0 y_0 p_0)
			(swap_0 x_15 x_0 y_0 q_0))
		(swap_0 (Node_0 x_14 y_0 x_15) x_0 y_0 (Node_0 p_0 x_0 q_0)))))
(assert (forall ((x_17 Tree_0) (x_18 Tree_0) (p_0 Tree_0) (x_1 Nat_0) (q_0 Tree_0) (x_0 Nat_0) (y_0 Nat_0))
	(=>	(and (diseqNat_0 x_1 x_0)
			(diseqNat_0 x_1 y_0)
			(swap_0 x_17 x_0 y_0 p_0)
			(swap_0 x_18 x_0 y_0 q_0))
		(swap_0 (Node_0 x_17 x_1 x_18) x_0 y_0 (Node_0 p_0 x_1 q_0)))))
(declare-fun elem_0 (Bool_0 Nat_0 list_0) Bool)
(assert (forall ((xs_0 list_0) (x_2 Nat_0))
	(elem_0 true_0 x_2 (cons_0 x_2 xs_0))))
(assert (forall ((x_20 Bool_0) (z_1 Nat_0) (xs_0 list_0) (x_2 Nat_0))
	(=>	(and (diseqNat_0 z_1 x_2)
			(elem_0 x_20 x_2 xs_0))
		(elem_0 x_20 x_2 (cons_0 z_1 xs_0)))))
(assert (forall ((x_2 Nat_0))
	(elem_0 false_0 x_2 nil_0)))
(declare-fun x_3 (list_0 list_0 list_0) Bool)
(assert (forall ((x_24 list_0) (z_2 Nat_0) (xs_1 list_0) (y_2 list_0))
	(=> (x_3 x_24 xs_1 y_2)
	    (x_3 (cons_0 z_2 x_24) (cons_0 z_2 xs_1) y_2))))
(assert (forall ((x_25 list_0))
	(x_3 x_25 nil_0 x_25)))
(declare-fun flatten_0 (list_0 Tree_0) Bool)
(assert (flatten_0 nil_0 Nil_1))
(assert (forall ((x_27 list_0) (x_28 list_0) (x_29 list_0) (x_30 list_0) (p_1 Tree_0) (y_3 Nat_0) (q_1 Tree_0))
	(=>	(and (flatten_0 x_28 p_1)
			(flatten_0 x_29 q_1)
			(x_3 x_30 (cons_0 y_3 nil_0) x_29)
			(x_3 x_27 x_28 x_30))
		(flatten_0 x_27 (Node_0 p_1 y_3 q_1)))))
(assert (forall ((x_37 list_0) (x_35 list_0) (x_32 Tree_0) (x_33 list_0) (x_34 Bool_0) (p_2 Tree_0) (a_0 Nat_0) (b_0 Nat_0))
	(=>	(and (diseqBool_0 x_34 true_0)
			(flatten_0 x_37 p_2)
			(elem_0 true_0 a_0 x_37)
			(flatten_0 x_35 p_2)
			(elem_0 true_0 b_0 x_35)
			(swap_0 x_32 a_0 b_0 p_2)
			(flatten_0 x_33 x_32)
			(elem_0 x_34 a_0 x_33))
		false)))
(assert (forall ((x_44 list_0) (x_42 list_0) (x_39 Tree_0) (x_40 list_0) (x_41 Bool_0) (p_2 Tree_0) (a_0 Nat_0) (b_0 Nat_0))
	(=>	(and (diseqBool_0 x_41 true_0)
			(flatten_0 x_44 p_2)
			(elem_0 true_0 a_0 x_44)
			(flatten_0 x_42 p_2)
			(elem_0 true_0 b_0 x_42)
			(swap_0 x_39 a_0 b_0 p_2)
			(flatten_0 x_40 x_39)
			(elem_0 x_41 b_0 x_40))
		false)))
(check-sat)
