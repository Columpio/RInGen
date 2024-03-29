(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_4 ) (Z_5 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_56 Nat_0))
	(unS_1 x_56 (Z_5 x_56))))
(assert (isZ_2 Z_4))
(assert (forall ((x_58 Nat_0))
	(isZ_3 (Z_5 x_58))))
(assert (forall ((x_59 Nat_0))
	(diseqNat_0 Z_4 (Z_5 x_59))))
(assert (forall ((x_60 Nat_0))
	(diseqNat_0 (Z_5 x_60) Z_4)))
(assert (forall ((x_61 Nat_0) (x_62 Nat_0))
	(=> (diseqNat_0 x_61 x_62)
	    (diseqNat_0 (Z_5 x_61) (Z_5 x_62)))))
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
	(add_0 y_7 Z_4 y_7)))
(assert (forall ((r_0 Nat_0) (x_54 Nat_0) (y_7 Nat_0))
	(=> (add_0 r_0 x_54 y_7)
	    (add_0 (Z_5 r_0) (Z_5 x_54) y_7))))
(assert (forall ((y_7 Nat_0))
	(minus_0 Z_4 Z_4 y_7)))
(assert (forall ((r_0 Nat_0) (x_54 Nat_0) (y_7 Nat_0))
	(=> (minus_0 r_0 x_54 y_7)
	    (minus_0 (Z_5 r_0) (Z_5 x_54) y_7))))
(assert (forall ((y_7 Nat_0))
	(le_0 Z_4 y_7)))
(assert (forall ((x_54 Nat_0) (y_7 Nat_0))
	(=> (le_0 x_54 y_7)
	    (le_0 (Z_5 x_54) (Z_5 y_7)))))
(assert (forall ((y_7 Nat_0))
	(ge_0 y_7 Z_4)))
(assert (forall ((x_54 Nat_0) (y_7 Nat_0))
	(=> (ge_0 x_54 y_7)
	    (ge_0 (Z_5 x_54) (Z_5 y_7)))))
(assert (forall ((y_7 Nat_0))
	(lt_0 Z_4 (Z_5 y_7))))
(assert (forall ((x_54 Nat_0) (y_7 Nat_0))
	(=> (lt_0 x_54 y_7)
	    (lt_0 (Z_5 x_54) (Z_5 y_7)))))
(assert (forall ((y_7 Nat_0))
	(gt_0 (Z_5 y_7) Z_4)))
(assert (forall ((x_54 Nat_0) (y_7 Nat_0))
	(=> (gt_0 x_54 y_7)
	    (gt_0 (Z_5 x_54) (Z_5 y_7)))))
(assert (forall ((y_7 Nat_0))
	(mult_0 Z_4 Z_4 y_7)))
(assert (forall ((r_0 Nat_0) (x_54 Nat_0) (y_7 Nat_0) (z_6 Nat_0))
	(=>	(and (mult_0 r_0 x_54 y_7)
			(add_0 z_6 r_0 y_7))
		(mult_0 z_6 (Z_5 x_54) y_7))))
(assert (forall ((x_54 Nat_0) (y_7 Nat_0))
	(=> (lt_0 x_54 y_7)
	    (div_0 Z_4 x_54 y_7))))
(assert (forall ((r_0 Nat_0) (x_54 Nat_0) (y_7 Nat_0) (z_6 Nat_0))
	(=>	(and (ge_0 x_54 y_7)
			(minus_0 z_6 x_54 y_7)
			(div_0 r_0 z_6 y_7))
		(div_0 (Z_5 r_0) x_54 y_7))))
(assert (forall ((x_54 Nat_0) (y_7 Nat_0))
	(=> (lt_0 x_54 y_7)
	    (mod_0 x_54 x_54 y_7))))
(assert (forall ((r_0 Nat_0) (x_54 Nat_0) (y_7 Nat_0) (z_6 Nat_0))
	(=>	(and (ge_0 x_54 y_7)
			(minus_0 z_6 x_54 y_7)
			(mod_0 r_0 z_6 y_7))
		(mod_0 r_0 x_54 y_7))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_2 (Nat_0 list_0) Bool)
(declare-fun tail_2 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_64 Nat_0) (x_65 list_0))
	(head_2 x_64 (cons_0 x_64 x_65))))
(assert (forall ((x_64 Nat_0) (x_65 list_0))
	(tail_2 x_65 (cons_0 x_64 x_65))))
(assert (isnil_0 nil_0))
(assert (forall ((x_67 Nat_0) (x_68 list_0))
	(iscons_0 (cons_0 x_67 x_68))))
(assert (forall ((x_69 Nat_0) (x_70 list_0))
	(diseqlist_0 nil_0 (cons_0 x_69 x_70))))
(assert (forall ((x_71 Nat_0) (x_72 list_0))
	(diseqlist_0 (cons_0 x_71 x_72) nil_0)))
(assert (forall ((x_73 Nat_0) (x_74 list_0) (x_75 Nat_0) (x_76 list_0))
	(=> (diseqNat_0 x_73 x_75)
	    (diseqlist_0 (cons_0 x_73 x_74) (cons_0 x_75 x_76)))))
(assert (forall ((x_73 Nat_0) (x_74 list_0) (x_75 Nat_0) (x_76 list_0))
	(=> (diseqlist_0 x_74 x_76)
	    (diseqlist_0 (cons_0 x_73 x_74) (cons_0 x_75 x_76)))))
(declare-datatypes ((Heap_0 0)) (((Node_0 (projNode_0 Heap_0) (projNode_1 Nat_0) (projNode_2 Heap_0)) (Nil_1 ))))
(declare-fun diseqHeap_0 (Heap_0 Heap_0) Bool)
(declare-fun projNode_3 (Heap_0 Heap_0) Bool)
(declare-fun projNode_4 (Nat_0 Heap_0) Bool)
(declare-fun projNode_5 (Heap_0 Heap_0) Bool)
(declare-fun isNode_0 (Heap_0) Bool)
(declare-fun isNil_1 (Heap_0) Bool)
(assert (forall ((x_77 Heap_0) (x_78 Nat_0) (x_79 Heap_0))
	(projNode_3 x_77 (Node_0 x_77 x_78 x_79))))
(assert (forall ((x_77 Heap_0) (x_78 Nat_0) (x_79 Heap_0))
	(projNode_4 x_78 (Node_0 x_77 x_78 x_79))))
(assert (forall ((x_77 Heap_0) (x_78 Nat_0) (x_79 Heap_0))
	(projNode_5 x_79 (Node_0 x_77 x_78 x_79))))
(assert (forall ((x_82 Heap_0) (x_83 Nat_0) (x_84 Heap_0))
	(isNode_0 (Node_0 x_82 x_83 x_84))))
(assert (isNil_1 Nil_1))
(assert (forall ((x_85 Heap_0) (x_86 Nat_0) (x_87 Heap_0))
	(diseqHeap_0 (Node_0 x_85 x_86 x_87) Nil_1)))
(assert (forall ((x_88 Heap_0) (x_89 Nat_0) (x_90 Heap_0))
	(diseqHeap_0 Nil_1 (Node_0 x_88 x_89 x_90))))
(assert (forall ((x_91 Heap_0) (x_92 Nat_0) (x_93 Heap_0) (x_94 Heap_0) (x_95 Nat_0) (x_96 Heap_0))
	(=> (diseqHeap_0 x_91 x_94)
	    (diseqHeap_0 (Node_0 x_91 x_92 x_93) (Node_0 x_94 x_95 x_96)))))
(assert (forall ((x_91 Heap_0) (x_92 Nat_0) (x_93 Heap_0) (x_94 Heap_0) (x_95 Nat_0) (x_96 Heap_0))
	(=> (diseqNat_0 x_92 x_95)
	    (diseqHeap_0 (Node_0 x_91 x_92 x_93) (Node_0 x_94 x_95 x_96)))))
(assert (forall ((x_91 Heap_0) (x_92 Nat_0) (x_93 Heap_0) (x_94 Heap_0) (x_95 Nat_0) (x_96 Heap_0))
	(=> (diseqHeap_0 x_93 x_96)
	    (diseqHeap_0 (Node_0 x_91 x_92 x_93) (Node_0 x_94 x_95 x_96)))))
(declare-datatypes ((list_1 0)) (((nil_2 ) (cons_1 (head_1 Heap_0) (tail_1 list_1)))))
(declare-fun diseqlist_1 (list_1 list_1) Bool)
(declare-fun head_3 (Heap_0 list_1) Bool)
(declare-fun tail_3 (list_1 list_1) Bool)
(declare-fun isnil_2 (list_1) Bool)
(declare-fun iscons_1 (list_1) Bool)
(assert (forall ((x_98 Heap_0) (x_99 list_1))
	(head_3 x_98 (cons_1 x_98 x_99))))
(assert (forall ((x_98 Heap_0) (x_99 list_1))
	(tail_3 x_99 (cons_1 x_98 x_99))))
(assert (isnil_2 nil_2))
(assert (forall ((x_101 Heap_0) (x_102 list_1))
	(iscons_1 (cons_1 x_101 x_102))))
(assert (forall ((x_103 Heap_0) (x_104 list_1))
	(diseqlist_1 nil_2 (cons_1 x_103 x_104))))
(assert (forall ((x_105 Heap_0) (x_106 list_1))
	(diseqlist_1 (cons_1 x_105 x_106) nil_2)))
(assert (forall ((x_107 Heap_0) (x_108 list_1) (x_109 Heap_0) (x_110 list_1))
	(=> (diseqHeap_0 x_107 x_109)
	    (diseqlist_1 (cons_1 x_107 x_108) (cons_1 x_109 x_110)))))
(assert (forall ((x_107 Heap_0) (x_108 list_1) (x_109 Heap_0) (x_110 list_1))
	(=> (diseqlist_1 x_108 x_110)
	    (diseqlist_1 (cons_1 x_107 x_108) (cons_1 x_109 x_110)))))
(declare-fun toHeap_0 (list_1 list_0) Bool)
(assert (forall ((x_16 list_1) (y_0 Nat_0) (z_0 list_0))
	(=> (toHeap_0 x_16 z_0)
	    (toHeap_0 (cons_1 (Node_0 Nil_1 y_0 Nil_1) x_16) (cons_0 y_0 z_0)))))
(assert (toHeap_0 nil_2 nil_0))
(declare-fun insert_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((z_1 Nat_0) (xs_0 list_0) (x_1 Nat_0))
	(=> (le_0 x_1 z_1)
	    (insert_0 (cons_0 x_1 (cons_0 z_1 xs_0)) x_1 (cons_0 z_1 xs_0)))))
(assert (forall ((x_20 list_0) (z_1 Nat_0) (xs_0 list_0) (x_1 Nat_0))
	(=>	(and (gt_0 x_1 z_1)
			(insert_0 x_20 x_1 xs_0))
		(insert_0 (cons_0 z_1 x_20) x_1 (cons_0 z_1 xs_0)))))
(assert (forall ((x_1 Nat_0))
	(insert_0 (cons_0 x_1 nil_0) x_1 nil_0)))
(declare-fun isort_0 (list_0 list_0) Bool)
(assert (forall ((x_22 list_0) (x_23 list_0) (y_2 Nat_0) (xs_1 list_0))
	(=>	(and (isort_0 x_23 xs_1)
			(insert_0 x_22 y_2 x_23))
		(isort_0 x_22 (cons_0 y_2 xs_1)))))
(assert (isort_0 nil_0 nil_0))
(declare-fun hmerge_0 (Heap_0 Heap_0 Heap_0) Bool)
(assert (forall ((x_26 Heap_0))
	(hmerge_0 x_26 Nil_1 x_26)))
(assert (forall ((z_2 Heap_0) (x_4 Nat_0) (x_5 Heap_0))
	(hmerge_0 (Node_0 z_2 x_4 x_5) (Node_0 z_2 x_4 x_5) Nil_1)))
(assert (forall ((x_29 Heap_0) (x_6 Heap_0) (x_7 Nat_0) (x_8 Heap_0) (z_2 Heap_0) (x_4 Nat_0) (x_5 Heap_0))
	(=>	(and (le_0 x_4 x_7)
			(hmerge_0 x_29 x_5 (Node_0 x_6 x_7 x_8)))
		(hmerge_0 (Node_0 x_29 x_4 z_2) (Node_0 z_2 x_4 x_5) (Node_0 x_6 x_7 x_8)))))
(assert (forall ((x_31 Heap_0) (x_6 Heap_0) (x_7 Nat_0) (x_8 Heap_0) (z_2 Heap_0) (x_4 Nat_0) (x_5 Heap_0))
	(=>	(and (gt_0 x_4 x_7)
			(hmerge_0 x_31 (Node_0 z_2 x_4 x_5) x_8))
		(hmerge_0 (Node_0 x_31 x_7 x_6) (Node_0 z_2 x_4 x_5) (Node_0 x_6 x_7 x_8)))))
(declare-fun hpairwise_0 (list_1 list_1) Bool)
(assert (forall ((x_33 Heap_0) (x_34 list_1) (q_0 Heap_0) (qs_0 list_1) (p_0 Heap_0))
	(=>	(and (hmerge_0 x_33 p_0 q_0)
			(hpairwise_0 x_34 qs_0))
		(hpairwise_0 (cons_1 x_33 x_34) (cons_1 p_0 (cons_1 q_0 qs_0))))))
(assert (forall ((p_0 Heap_0))
	(hpairwise_0 (cons_1 p_0 nil_2) (cons_1 p_0 nil_2))))
(assert (hpairwise_0 nil_2 nil_2))
(declare-fun hmerging_0 (Heap_0 list_1) Bool)
(assert (forall ((x_37 Heap_0) (x_38 list_1) (z_3 Heap_0) (x_11 list_1) (p_1 Heap_0))
	(=>	(and (hpairwise_0 x_38 (cons_1 p_1 (cons_1 z_3 x_11)))
			(hmerging_0 x_37 x_38))
		(hmerging_0 x_37 (cons_1 p_1 (cons_1 z_3 x_11))))))
(assert (forall ((p_1 Heap_0))
	(hmerging_0 p_1 (cons_1 p_1 nil_2))))
(assert (hmerging_0 Nil_1 nil_2))
(declare-fun toHeap_1 (Heap_0 list_0) Bool)
(assert (forall ((x_42 Heap_0) (x_43 list_1) (x_12 list_0))
	(=>	(and (toHeap_0 x_43 x_12)
			(hmerging_0 x_42 x_43))
		(toHeap_1 x_42 x_12))))
(declare-fun toList_0 (list_0 Heap_0) Bool)
(assert (toList_0 nil_0 Nil_1))
(assert (forall ((x_47 Heap_0) (x_48 list_0) (p_2 Heap_0) (y_6 Nat_0) (q_1 Heap_0))
	(=>	(and (hmerge_0 x_47 p_2 q_1)
			(toList_0 x_48 x_47))
		(toList_0 (cons_0 y_6 x_48) (Node_0 p_2 y_6 q_1)))))
(declare-fun hsort_0 (list_0 list_0) Bool)
(assert (forall ((x_49 list_0) (x_50 Heap_0) (x_14 list_0))
	(=>	(and (toHeap_1 x_50 x_14)
			(toList_0 x_49 x_50))
		(hsort_0 x_49 x_14))))
(assert (forall ((x_52 list_0) (x_53 list_0) (xs_2 list_0))
	(=>	(and (diseqlist_0 x_52 x_53)
			(hsort_0 x_52 xs_2)
			(isort_0 x_53 xs_2))
		false)))
(check-sat)
