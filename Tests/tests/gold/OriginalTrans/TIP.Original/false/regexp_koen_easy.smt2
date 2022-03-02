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
(declare-datatypes ((T_0 0)) (((A_0 ) (B_0 ) (C_0 ))))
(declare-fun diseqT_0 (T_0 T_0) Bool)
(declare-fun isA_0 (T_0) Bool)
(declare-fun isB_0 (T_0) Bool)
(declare-fun isC_0 (T_0) Bool)
(assert (isA_0 A_0))
(assert (isB_0 B_0))
(assert (isC_0 C_0))
(assert (diseqT_0 A_0 B_0))
(assert (diseqT_0 A_0 C_0))
(assert (diseqT_0 B_0 A_0))
(assert (diseqT_0 C_0 A_0))
(assert (diseqT_0 B_0 C_0))
(assert (diseqT_0 C_0 B_0))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 T_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (T_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_50 T_0) (x_51 list_0))
	(head_1 x_50 (cons_0 x_50 x_51))))
(assert (forall ((x_50 T_0) (x_51 list_0))
	(tail_1 x_51 (cons_0 x_50 x_51))))
(assert (isnil_0 nil_0))
(assert (forall ((x_53 T_0) (x_54 list_0))
	(iscons_0 (cons_0 x_53 x_54))))
(assert (forall ((x_55 T_0) (x_56 list_0))
	(diseqlist_0 nil_0 (cons_0 x_55 x_56))))
(assert (forall ((x_57 T_0) (x_58 list_0))
	(diseqlist_0 (cons_0 x_57 x_58) nil_0)))
(assert (forall ((x_59 T_0) (x_60 list_0) (x_61 T_0) (x_62 list_0))
	(=> (diseqT_0 x_59 x_61)
	    (diseqlist_0 (cons_0 x_59 x_60) (cons_0 x_61 x_62)))))
(assert (forall ((x_59 T_0) (x_60 list_0) (x_61 T_0) (x_62 list_0))
	(=> (diseqlist_0 x_60 x_62)
	    (diseqlist_0 (cons_0 x_59 x_60) (cons_0 x_61 x_62)))))
(declare-datatypes ((R_0 0)) (((Nil_1 ) (Eps_0 ) (Atom_0 (projAtom_0 T_0)) (x_0 (proj_0 R_0) (proj_1 R_0)) (x_1 (proj_2 R_0) (proj_3 R_0)) (Star_0 (projStar_0 R_0)))))
(declare-fun diseqR_0 (R_0 R_0) Bool)
(declare-fun projAtom_1 (T_0 R_0) Bool)
(declare-fun proj_4 (R_0 R_0) Bool)
(declare-fun proj_5 (R_0 R_0) Bool)
(declare-fun proj_6 (R_0 R_0) Bool)
(declare-fun proj_7 (R_0 R_0) Bool)
(declare-fun projStar_1 (R_0 R_0) Bool)
(declare-fun isNil_1 (R_0) Bool)
(declare-fun isEps_0 (R_0) Bool)
(declare-fun isAtom_0 (R_0) Bool)
(declare-fun isx_0 (R_0) Bool)
(declare-fun isx_1 (R_0) Bool)
(declare-fun isStar_0 (R_0) Bool)
(assert (forall ((x_65 T_0))
	(projAtom_1 x_65 (Atom_0 x_65))))
(assert (forall ((x_67 R_0) (x_68 R_0))
	(proj_4 x_67 (x_0 x_67 x_68))))
(assert (forall ((x_67 R_0) (x_68 R_0))
	(proj_5 x_68 (x_0 x_67 x_68))))
(assert (forall ((x_70 R_0) (x_71 R_0))
	(proj_6 x_70 (x_1 x_70 x_71))))
(assert (forall ((x_70 R_0) (x_71 R_0))
	(proj_7 x_71 (x_1 x_70 x_71))))
(assert (forall ((x_73 R_0))
	(projStar_1 x_73 (Star_0 x_73))))
(assert (isNil_1 Nil_1))
(assert (isEps_0 Eps_0))
(assert (forall ((x_75 T_0))
	(isAtom_0 (Atom_0 x_75))))
(assert (forall ((x_76 R_0) (x_77 R_0))
	(isx_0 (x_0 x_76 x_77))))
(assert (forall ((x_78 R_0) (x_79 R_0))
	(isx_1 (x_1 x_78 x_79))))
(assert (forall ((x_80 R_0))
	(isStar_0 (Star_0 x_80))))
(assert (diseqR_0 Nil_1 Eps_0))
(assert (forall ((x_81 T_0))
	(diseqR_0 Nil_1 (Atom_0 x_81))))
(assert (forall ((x_82 R_0) (x_83 R_0))
	(diseqR_0 Nil_1 (x_0 x_82 x_83))))
(assert (forall ((x_84 R_0) (x_85 R_0))
	(diseqR_0 Nil_1 (x_1 x_84 x_85))))
(assert (forall ((x_86 R_0))
	(diseqR_0 Nil_1 (Star_0 x_86))))
(assert (diseqR_0 Eps_0 Nil_1))
(assert (forall ((x_87 T_0))
	(diseqR_0 (Atom_0 x_87) Nil_1)))
(assert (forall ((x_88 R_0) (x_89 R_0))
	(diseqR_0 (x_0 x_88 x_89) Nil_1)))
(assert (forall ((x_90 R_0) (x_91 R_0))
	(diseqR_0 (x_1 x_90 x_91) Nil_1)))
(assert (forall ((x_92 R_0))
	(diseqR_0 (Star_0 x_92) Nil_1)))
(assert (forall ((x_93 T_0))
	(diseqR_0 Eps_0 (Atom_0 x_93))))
(assert (forall ((x_94 R_0) (x_95 R_0))
	(diseqR_0 Eps_0 (x_0 x_94 x_95))))
(assert (forall ((x_96 R_0) (x_97 R_0))
	(diseqR_0 Eps_0 (x_1 x_96 x_97))))
(assert (forall ((x_98 R_0))
	(diseqR_0 Eps_0 (Star_0 x_98))))
(assert (forall ((x_99 T_0))
	(diseqR_0 (Atom_0 x_99) Eps_0)))
(assert (forall ((x_100 R_0) (x_101 R_0))
	(diseqR_0 (x_0 x_100 x_101) Eps_0)))
(assert (forall ((x_102 R_0) (x_103 R_0))
	(diseqR_0 (x_1 x_102 x_103) Eps_0)))
(assert (forall ((x_104 R_0))
	(diseqR_0 (Star_0 x_104) Eps_0)))
(assert (forall ((x_105 T_0) (x_106 R_0) (x_107 R_0))
	(diseqR_0 (Atom_0 x_105) (x_0 x_106 x_107))))
(assert (forall ((x_108 T_0) (x_109 R_0) (x_110 R_0))
	(diseqR_0 (Atom_0 x_108) (x_1 x_109 x_110))))
(assert (forall ((x_111 T_0) (x_112 R_0))
	(diseqR_0 (Atom_0 x_111) (Star_0 x_112))))
(assert (forall ((x_113 R_0) (x_114 R_0) (x_115 T_0))
	(diseqR_0 (x_0 x_113 x_114) (Atom_0 x_115))))
(assert (forall ((x_116 R_0) (x_117 R_0) (x_118 T_0))
	(diseqR_0 (x_1 x_116 x_117) (Atom_0 x_118))))
(assert (forall ((x_119 R_0) (x_120 T_0))
	(diseqR_0 (Star_0 x_119) (Atom_0 x_120))))
(assert (forall ((x_121 R_0) (x_122 R_0) (x_123 R_0) (x_124 R_0))
	(diseqR_0 (x_0 x_121 x_122) (x_1 x_123 x_124))))
(assert (forall ((x_125 R_0) (x_126 R_0) (x_127 R_0))
	(diseqR_0 (x_0 x_125 x_126) (Star_0 x_127))))
(assert (forall ((x_128 R_0) (x_129 R_0) (x_130 R_0) (x_131 R_0))
	(diseqR_0 (x_1 x_128 x_129) (x_0 x_130 x_131))))
(assert (forall ((x_132 R_0) (x_133 R_0) (x_134 R_0))
	(diseqR_0 (Star_0 x_132) (x_0 x_133 x_134))))
(assert (forall ((x_135 R_0) (x_136 R_0) (x_137 R_0))
	(diseqR_0 (x_1 x_135 x_136) (Star_0 x_137))))
(assert (forall ((x_138 R_0) (x_139 R_0) (x_140 R_0))
	(diseqR_0 (Star_0 x_138) (x_1 x_139 x_140))))
(assert (forall ((x_141 T_0) (x_142 T_0))
	(=> (diseqT_0 x_141 x_142)
	    (diseqR_0 (Atom_0 x_141) (Atom_0 x_142)))))
(assert (forall ((x_143 R_0) (x_144 R_0) (x_145 R_0) (x_146 R_0))
	(=> (diseqR_0 x_143 x_145)
	    (diseqR_0 (x_0 x_143 x_144) (x_0 x_145 x_146)))))
(assert (forall ((x_143 R_0) (x_144 R_0) (x_145 R_0) (x_146 R_0))
	(=> (diseqR_0 x_144 x_146)
	    (diseqR_0 (x_0 x_143 x_144) (x_0 x_145 x_146)))))
(assert (forall ((x_147 R_0) (x_148 R_0) (x_149 R_0) (x_150 R_0))
	(=> (diseqR_0 x_147 x_149)
	    (diseqR_0 (x_1 x_147 x_148) (x_1 x_149 x_150)))))
(assert (forall ((x_147 R_0) (x_148 R_0) (x_149 R_0) (x_150 R_0))
	(=> (diseqR_0 x_148 x_150)
	    (diseqR_0 (x_1 x_147 x_148) (x_1 x_149 x_150)))))
(assert (forall ((x_151 R_0) (x_152 R_0))
	(=> (diseqR_0 x_151 x_152)
	    (diseqR_0 (Star_0 x_151) (Star_0 x_152)))))
(declare-fun eps_1 (Bool_0 R_0) Bool)
(assert (forall ((y_0 R_0))
	(eps_1 true_0 (Star_0 y_0))))
(assert (forall ((x_41 Bool_0) (x_10 Bool_0) (x_11 Bool_0) (r_1 R_0) (q_1 R_0))
	(=>	(and (eps_1 x_10 r_1)
			(eps_1 x_11 q_1)
			(and_0 x_41 x_10 x_11))
		(eps_1 x_41 (x_1 r_1 q_1)))))
(assert (forall ((x_12 Bool_0) (x_13 Bool_0) (x_14 Bool_0) (p_0 R_0) (q_0 R_0))
	(=>	(and (eps_1 x_13 p_0)
			(eps_1 x_14 q_0)
			(or_0 x_12 x_13 x_14))
		(eps_1 x_12 (x_0 p_0 q_0)))))
(assert (eps_1 true_0 Eps_0))
(assert (forall ((x_3 R_0) (x_7 T_0))
	(eps_1 false_0 (Atom_0 x_7))))
(assert (forall ((x_3 R_0))
	(eps_1 false_0 Nil_1)))
(declare-fun step_0 (R_0 R_0 T_0) Bool)
(assert (forall ((x_19 R_0) (p_2 R_0) (y_1 T_0))
	(=> (step_0 x_19 p_2 y_1)
	    (step_0 (x_1 x_19 (Star_0 p_2)) (Star_0 p_2) y_1))))
(assert (forall ((x_22 R_0) (x_23 R_0) (r_2 R_0) (q_3 R_0) (y_1 T_0))
	(=>	(and (step_0 x_22 r_2 y_1)
			(step_0 x_23 q_3 y_1)
			(eps_1 true_0 r_2))
		(step_0 (x_0 (x_1 x_22 q_3) x_23) (x_1 r_2 q_3) y_1))))
(assert (forall ((x_26 R_0) (x_24 Bool_0) (r_2 R_0) (q_3 R_0) (y_1 T_0))
	(=>	(and (diseqBool_0 x_24 true_0)
			(step_0 x_26 r_2 y_1)
			(eps_1 x_24 r_2))
		(step_0 (x_0 (x_1 x_26 q_3) Nil_1) (x_1 r_2 q_3) y_1))))
(assert (forall ((x_28 R_0) (x_29 R_0) (p_1 R_0) (q_2 R_0) (y_1 T_0))
	(=>	(and (step_0 x_28 p_1 y_1)
			(step_0 x_29 q_2 y_1))
		(step_0 (x_0 x_28 x_29) (x_0 p_1 q_2) y_1))))
(assert (forall ((b_1 T_0))
	(step_0 Eps_0 (Atom_0 b_1) b_1)))
(assert (forall ((b_1 T_0) (y_1 T_0))
	(=> (diseqT_0 b_1 y_1)
	    (step_0 Nil_1 (Atom_0 b_1) y_1))))
(assert (forall ((x_5 R_0) (y_1 T_0))
	(step_0 Nil_1 Eps_0 y_1)))
(assert (forall ((x_5 R_0) (y_1 T_0))
	(step_0 Nil_1 Nil_1 y_1)))
(declare-fun rec_0 (Bool_0 R_0 list_0) Bool)
(assert (forall ((x_34 Bool_0) (x_35 R_0) (z_0 T_0) (xs_0 list_0) (x_6 R_0))
	(=>	(and (step_0 x_35 x_6 z_0)
			(rec_0 x_34 x_35 xs_0))
		(rec_0 x_34 x_6 (cons_0 z_0 xs_0)))))
(assert (forall ((x_37 Bool_0) (x_6 R_0))
	(=> (eps_1 x_37 x_6)
	    (rec_0 x_37 x_6 nil_0))))
(assert (forall ((x_39 Bool_0) (x_40 Bool_0) (p_3 R_0) (q_4 R_0) (a_1 T_0) (b_2 T_0))
	(=>	(and (diseqBool_0 x_39 x_40)
			(rec_0 x_39 (x_1 p_3 q_4) (cons_0 a_1 (cons_0 b_2 nil_0)))
			(rec_0 x_40 (x_1 q_4 p_3) (cons_0 a_1 (cons_0 b_2 nil_0))))
		false)))
(check-sat)