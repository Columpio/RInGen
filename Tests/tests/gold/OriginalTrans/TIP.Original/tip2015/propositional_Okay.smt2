(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_10 ) (Z_11 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_105 Nat_0))
	(unS_1 x_105 (Z_11 x_105))))
(assert (isZ_2 Z_10))
(assert (forall ((x_107 Nat_0))
	(isZ_3 (Z_11 x_107))))
(assert (forall ((x_108 Nat_0))
	(diseqNat_0 Z_10 (Z_11 x_108))))
(assert (forall ((x_109 Nat_0))
	(diseqNat_0 (Z_11 x_109) Z_10)))
(assert (forall ((x_110 Nat_0) (x_111 Nat_0))
	(=> (diseqNat_0 x_110 x_111)
	    (diseqNat_0 (Z_11 x_110) (Z_11 x_111)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_18 Nat_0))
	(add_0 y_18 Z_10 y_18)))
(assert (forall ((r_1 Nat_0) (x_103 Nat_0) (y_18 Nat_0))
	(=> (add_0 r_1 x_103 y_18)
	    (add_0 (Z_11 r_1) (Z_11 x_103) y_18))))
(assert (forall ((y_18 Nat_0))
	(minus_0 Z_10 Z_10 y_18)))
(assert (forall ((r_1 Nat_0) (x_103 Nat_0) (y_18 Nat_0))
	(=> (minus_0 r_1 x_103 y_18)
	    (minus_0 (Z_11 r_1) (Z_11 x_103) y_18))))
(assert (forall ((y_18 Nat_0))
	(le_0 Z_10 y_18)))
(assert (forall ((x_103 Nat_0) (y_18 Nat_0))
	(=> (le_0 x_103 y_18)
	    (le_0 (Z_11 x_103) (Z_11 y_18)))))
(assert (forall ((y_18 Nat_0))
	(ge_0 y_18 Z_10)))
(assert (forall ((x_103 Nat_0) (y_18 Nat_0))
	(=> (ge_0 x_103 y_18)
	    (ge_0 (Z_11 x_103) (Z_11 y_18)))))
(assert (forall ((y_18 Nat_0))
	(lt_0 Z_10 (Z_11 y_18))))
(assert (forall ((x_103 Nat_0) (y_18 Nat_0))
	(=> (lt_0 x_103 y_18)
	    (lt_0 (Z_11 x_103) (Z_11 y_18)))))
(assert (forall ((y_18 Nat_0))
	(gt_0 (Z_11 y_18) Z_10)))
(assert (forall ((x_103 Nat_0) (y_18 Nat_0))
	(=> (gt_0 x_103 y_18)
	    (gt_0 (Z_11 x_103) (Z_11 y_18)))))
(assert (forall ((y_18 Nat_0))
	(mult_0 Z_10 Z_10 y_18)))
(assert (forall ((r_1 Nat_0) (x_103 Nat_0) (y_18 Nat_0) (z_12 Nat_0))
	(=>	(and (mult_0 r_1 x_103 y_18)
			(add_0 z_12 r_1 y_18))
		(mult_0 z_12 (Z_11 x_103) y_18))))
(assert (forall ((x_103 Nat_0) (y_18 Nat_0))
	(=> (lt_0 x_103 y_18)
	    (div_0 Z_10 x_103 y_18))))
(assert (forall ((r_1 Nat_0) (x_103 Nat_0) (y_18 Nat_0) (z_12 Nat_0))
	(=>	(and (ge_0 x_103 y_18)
			(minus_0 z_12 x_103 y_18)
			(div_0 r_1 z_12 y_18))
		(div_0 (Z_11 r_1) x_103 y_18))))
(assert (forall ((x_103 Nat_0) (y_18 Nat_0))
	(=> (lt_0 x_103 y_18)
	    (mod_0 x_103 x_103 y_18))))
(assert (forall ((r_1 Nat_0) (x_103 Nat_0) (y_18 Nat_0) (z_12 Nat_0))
	(=>	(and (ge_0 x_103 y_18)
			(minus_0 z_12 x_103 y_18)
			(mod_0 r_1 z_12 y_18))
		(mod_0 r_1 x_103 y_18))))
(declare-datatypes ((Bool_0 0)) (((false_0 ) (true_0 ))))
(declare-fun diseqBool_0 (Bool_0 Bool_0) Bool)
(declare-fun isfalse_1 (Bool_0) Bool)
(declare-fun istrue_1 (Bool_0) Bool)
(assert (isfalse_1 false_0))
(assert (istrue_1 true_0))
(assert (diseqBool_0 false_0 true_0))
(assert (diseqBool_0 true_0 false_0))
(declare-fun and_0 (Bool_0 Bool_0 Bool_0) Bool)
(declare-fun or_1 (Bool_0 Bool_0 Bool_0) Bool)
(declare-fun hence_0 (Bool_0 Bool_0 Bool_0) Bool)
(declare-fun not_1 (Bool_0 Bool_0) Bool)
(assert (and_0 false_0 false_0 false_0))
(assert (and_0 false_0 true_0 false_0))
(assert (and_0 false_0 false_0 true_0))
(assert (and_0 true_0 true_0 true_0))
(assert (or_1 false_0 false_0 false_0))
(assert (or_1 true_0 true_0 false_0))
(assert (or_1 true_0 false_0 true_0))
(assert (or_1 true_0 true_0 true_0))
(assert (hence_0 true_0 false_0 false_0))
(assert (hence_0 false_0 true_0 false_0))
(assert (hence_0 true_0 false_0 true_0))
(assert (hence_0 true_0 true_0 true_0))
(assert (not_1 true_0 false_0))
(assert (not_1 false_0 true_0))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 Nat_0) (projpair_1 Bool_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (Nat_0 pair_0) Bool)
(declare-fun projpair_3 (Bool_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_114 Nat_0) (x_115 Bool_0))
	(projpair_2 x_114 (pair_1 x_114 x_115))))
(assert (forall ((x_114 Nat_0) (x_115 Bool_0))
	(projpair_3 x_115 (pair_1 x_114 x_115))))
(assert (forall ((x_117 Nat_0) (x_118 Bool_0))
	(ispair_0 (pair_1 x_117 x_118))))
(assert (forall ((x_119 Nat_0) (x_120 Bool_0) (x_121 Nat_0) (x_122 Bool_0))
	(=> (diseqNat_0 x_119 x_121)
	    (diseqpair_0 (pair_1 x_119 x_120) (pair_1 x_121 x_122)))))
(assert (forall ((x_119 Nat_0) (x_120 Bool_0) (x_121 Nat_0) (x_122 Bool_0))
	(=> (diseqBool_0 x_120 x_122)
	    (diseqpair_0 (pair_1 x_119 x_120) (pair_1 x_121 x_122)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Bool_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_4 (Bool_0 list_0) Bool)
(declare-fun tail_4 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_124 Bool_0) (x_125 list_0))
	(head_4 x_124 (cons_0 x_124 x_125))))
(assert (forall ((x_124 Bool_0) (x_125 list_0))
	(tail_4 x_125 (cons_0 x_124 x_125))))
(assert (isnil_0 nil_0))
(assert (forall ((x_127 Bool_0) (x_128 list_0))
	(iscons_0 (cons_0 x_127 x_128))))
(assert (forall ((x_129 Bool_0) (x_130 list_0))
	(diseqlist_0 nil_0 (cons_0 x_129 x_130))))
(assert (forall ((x_131 Bool_0) (x_132 list_0))
	(diseqlist_0 (cons_0 x_131 x_132) nil_0)))
(assert (forall ((x_133 Bool_0) (x_134 list_0) (x_135 Bool_0) (x_136 list_0))
	(=> (diseqBool_0 x_133 x_135)
	    (diseqlist_0 (cons_0 x_133 x_134) (cons_0 x_135 x_136)))))
(assert (forall ((x_133 Bool_0) (x_134 list_0) (x_135 Bool_0) (x_136 list_0))
	(=> (diseqlist_0 x_134 x_136)
	    (diseqlist_0 (cons_0 x_133 x_134) (cons_0 x_135 x_136)))))
(declare-datatypes ((list_1 0)) (((nil_1 ) (cons_1 (head_1 Nat_0) (tail_1 list_1)))))
(declare-fun diseqlist_1 (list_1 list_1) Bool)
(declare-fun head_5 (Nat_0 list_1) Bool)
(declare-fun tail_5 (list_1 list_1) Bool)
(declare-fun isnil_1 (list_1) Bool)
(declare-fun iscons_1 (list_1) Bool)
(assert (forall ((x_138 Nat_0) (x_139 list_1))
	(head_5 x_138 (cons_1 x_138 x_139))))
(assert (forall ((x_138 Nat_0) (x_139 list_1))
	(tail_5 x_139 (cons_1 x_138 x_139))))
(assert (isnil_1 nil_1))
(assert (forall ((x_141 Nat_0) (x_142 list_1))
	(iscons_1 (cons_1 x_141 x_142))))
(assert (forall ((x_143 Nat_0) (x_144 list_1))
	(diseqlist_1 nil_1 (cons_1 x_143 x_144))))
(assert (forall ((x_145 Nat_0) (x_146 list_1))
	(diseqlist_1 (cons_1 x_145 x_146) nil_1)))
(assert (forall ((x_147 Nat_0) (x_148 list_1) (x_149 Nat_0) (x_150 list_1))
	(=> (diseqNat_0 x_147 x_149)
	    (diseqlist_1 (cons_1 x_147 x_148) (cons_1 x_149 x_150)))))
(assert (forall ((x_147 Nat_0) (x_148 list_1) (x_149 Nat_0) (x_150 list_1))
	(=> (diseqlist_1 x_148 x_150)
	    (diseqlist_1 (cons_1 x_147 x_148) (cons_1 x_149 x_150)))))
(declare-datatypes ((list_2 0)) (((nil_2 ) (cons_2 (head_2 pair_0) (tail_2 list_2)))))
(declare-fun diseqlist_2 (list_2 list_2) Bool)
(declare-fun head_6 (pair_0 list_2) Bool)
(declare-fun tail_6 (list_2 list_2) Bool)
(declare-fun isnil_2 (list_2) Bool)
(declare-fun iscons_2 (list_2) Bool)
(assert (forall ((x_152 pair_0) (x_153 list_2))
	(head_6 x_152 (cons_2 x_152 x_153))))
(assert (forall ((x_152 pair_0) (x_153 list_2))
	(tail_6 x_153 (cons_2 x_152 x_153))))
(assert (isnil_2 nil_2))
(assert (forall ((x_155 pair_0) (x_156 list_2))
	(iscons_2 (cons_2 x_155 x_156))))
(assert (forall ((x_157 pair_0) (x_158 list_2))
	(diseqlist_2 nil_2 (cons_2 x_157 x_158))))
(assert (forall ((x_159 pair_0) (x_160 list_2))
	(diseqlist_2 (cons_2 x_159 x_160) nil_2)))
(assert (forall ((x_161 pair_0) (x_162 list_2) (x_163 pair_0) (x_164 list_2))
	(=> (diseqpair_0 x_161 x_163)
	    (diseqlist_2 (cons_2 x_161 x_162) (cons_2 x_163 x_164)))))
(assert (forall ((x_161 pair_0) (x_162 list_2) (x_163 pair_0) (x_164 list_2))
	(=> (diseqlist_2 x_162 x_164)
	    (diseqlist_2 (cons_2 x_161 x_162) (cons_2 x_163 x_164)))))
(declare-datatypes ((list_3 0)) (((nil_3 ) (cons_3 (head_3 list_2) (tail_3 list_3)))))
(declare-fun diseqlist_3 (list_3 list_3) Bool)
(declare-fun head_7 (list_2 list_3) Bool)
(declare-fun tail_7 (list_3 list_3) Bool)
(declare-fun isnil_3 (list_3) Bool)
(declare-fun iscons_3 (list_3) Bool)
(assert (forall ((x_166 list_2) (x_167 list_3))
	(head_7 x_166 (cons_3 x_166 x_167))))
(assert (forall ((x_166 list_2) (x_167 list_3))
	(tail_7 x_167 (cons_3 x_166 x_167))))
(assert (isnil_3 nil_3))
(assert (forall ((x_169 list_2) (x_170 list_3))
	(iscons_3 (cons_3 x_169 x_170))))
(assert (forall ((x_171 list_2) (x_172 list_3))
	(diseqlist_3 nil_3 (cons_3 x_171 x_172))))
(assert (forall ((x_173 list_2) (x_174 list_3))
	(diseqlist_3 (cons_3 x_173 x_174) nil_3)))
(assert (forall ((x_175 list_2) (x_176 list_3) (x_177 list_2) (x_178 list_3))
	(=> (diseqlist_2 x_175 x_177)
	    (diseqlist_3 (cons_3 x_175 x_176) (cons_3 x_177 x_178)))))
(assert (forall ((x_175 list_2) (x_176 list_3) (x_177 list_2) (x_178 list_3))
	(=> (diseqlist_3 x_176 x_178)
	    (diseqlist_3 (cons_3 x_175 x_176) (cons_3 x_177 x_178)))))
(declare-datatypes ((Form_0 0)) (((x_0 (proj_0 Form_0) (proj_1 Form_0)) (Not_0 (projNot_0 Form_0)) (Var_0 (projVar_0 Nat_0)))))
(declare-fun diseqForm_0 (Form_0 Form_0) Bool)
(declare-fun proj_2 (Form_0 Form_0) Bool)
(declare-fun proj_3 (Form_0 Form_0) Bool)
(declare-fun projNot_1 (Form_0 Form_0) Bool)
(declare-fun projVar_1 (Nat_0 Form_0) Bool)
(declare-fun isx_0 (Form_0) Bool)
(declare-fun isNot_0 (Form_0) Bool)
(declare-fun isVar_0 (Form_0) Bool)
(assert (forall ((x_179 Form_0) (x_180 Form_0))
	(proj_2 x_179 (x_0 x_179 x_180))))
(assert (forall ((x_179 Form_0) (x_180 Form_0))
	(proj_3 x_180 (x_0 x_179 x_180))))
(assert (forall ((x_182 Form_0))
	(projNot_1 x_182 (Not_0 x_182))))
(assert (forall ((x_184 Nat_0))
	(projVar_1 x_184 (Var_0 x_184))))
(assert (forall ((x_186 Form_0) (x_187 Form_0))
	(isx_0 (x_0 x_186 x_187))))
(assert (forall ((x_188 Form_0))
	(isNot_0 (Not_0 x_188))))
(assert (forall ((x_189 Nat_0))
	(isVar_0 (Var_0 x_189))))
(assert (forall ((x_190 Form_0) (x_191 Form_0) (x_192 Form_0))
	(diseqForm_0 (x_0 x_190 x_191) (Not_0 x_192))))
(assert (forall ((x_193 Form_0) (x_194 Form_0) (x_195 Nat_0))
	(diseqForm_0 (x_0 x_193 x_194) (Var_0 x_195))))
(assert (forall ((x_196 Form_0) (x_197 Form_0) (x_198 Form_0))
	(diseqForm_0 (Not_0 x_196) (x_0 x_197 x_198))))
(assert (forall ((x_199 Nat_0) (x_200 Form_0) (x_201 Form_0))
	(diseqForm_0 (Var_0 x_199) (x_0 x_200 x_201))))
(assert (forall ((x_202 Form_0) (x_203 Nat_0))
	(diseqForm_0 (Not_0 x_202) (Var_0 x_203))))
(assert (forall ((x_204 Nat_0) (x_205 Form_0))
	(diseqForm_0 (Var_0 x_204) (Not_0 x_205))))
(assert (forall ((x_206 Form_0) (x_207 Form_0) (x_208 Form_0) (x_209 Form_0))
	(=> (diseqForm_0 x_206 x_208)
	    (diseqForm_0 (x_0 x_206 x_207) (x_0 x_208 x_209)))))
(assert (forall ((x_206 Form_0) (x_207 Form_0) (x_208 Form_0) (x_209 Form_0))
	(=> (diseqForm_0 x_207 x_209)
	    (diseqForm_0 (x_0 x_206 x_207) (x_0 x_208 x_209)))))
(assert (forall ((x_210 Form_0) (x_211 Form_0))
	(=> (diseqForm_0 x_210 x_211)
	    (diseqForm_0 (Not_0 x_210) (Not_0 x_211)))))
(assert (forall ((x_212 Nat_0) (x_213 Nat_0))
	(=> (diseqNat_0 x_212 x_213)
	    (diseqForm_0 (Var_0 x_212) (Var_0 x_213)))))
(declare-fun or_0 (Bool_0 list_0) Bool)
(assert (forall ((x_25 Bool_0) (x_26 Bool_0) (y_0 Bool_0) (xs_0 list_0))
	(=>	(and (or_0 x_26 xs_0)
			(or_1 x_25 y_0 x_26))
		(or_0 x_25 (cons_0 y_0 xs_0)))))
(assert (or_0 false_0 nil_0))
(declare-fun okay_0 (list_1 list_2) Bool)
(assert (forall ((x_29 list_1) (z_0 Nat_0) (y_2 Bool_0) (xs_1 list_2))
	(=> (okay_0 x_29 xs_1)
	    (okay_0 (cons_1 z_0 x_29) (cons_2 (pair_1 z_0 y_2) xs_1)))))
(assert (okay_0 nil_1 nil_2))
(declare-fun models_0 (list_2 Nat_0 list_2) Bool)
(assert (forall ((x_32 list_2) (x_4 Nat_0) (y_4 Bool_0) (xs_2 list_2) (x_3 Nat_0))
	(=>	(and (diseqNat_0 x_3 x_4)
			(models_0 x_32 x_3 xs_2))
		(models_0 (cons_2 (pair_1 x_4 y_4) x_32) x_3 (cons_2 (pair_1 x_4 y_4) xs_2)))))
(assert (forall ((x_33 list_2) (y_4 Bool_0) (xs_2 list_2) (x_3 Nat_0))
	(=> (models_0 x_33 x_3 xs_2)
	    (models_0 x_33 x_3 (cons_2 (pair_1 x_3 y_4) xs_2)))))
(assert (forall ((x_3 Nat_0))
	(models_0 nil_2 x_3 nil_2)))
(declare-fun models_1 (list_0 Nat_0 list_2) Bool)
(assert (forall ((x_36 list_0) (y_6 Nat_0) (x_6 list_2) (x_5 Nat_0))
	(=> (models_1 x_36 x_5 x_6)
	    (models_1 x_36 x_5 (cons_2 (pair_1 y_6 true_0) x_6)))))
(assert (forall ((x_39 list_0) (x_7 Bool_0) (x_6 list_2) (x_5 Nat_0))
	(=>	(and (diseqBool_0 x_7 true_0)
			(models_1 x_39 x_5 x_6))
		(models_1 (cons_0 true_0 x_39) x_5 (cons_2 (pair_1 x_5 x_7) x_6)))))
(assert (forall ((x_41 list_0) (y_6 Nat_0) (x_7 Bool_0) (x_6 list_2) (x_5 Nat_0))
	(=>	(and (diseqNat_0 x_5 y_6)
			(diseqBool_0 x_7 true_0)
			(models_1 x_41 x_5 x_6))
		(models_1 (cons_0 false_0 x_41) x_5 (cons_2 (pair_1 y_6 x_7) x_6)))))
(assert (forall ((x_5 Nat_0))
	(models_1 nil_0 x_5 nil_2)))
(declare-fun models_2 (list_0 Nat_0 list_2) Bool)
(assert (forall ((x_44 list_0) (x_9 list_2) (x_8 Nat_0))
	(=> (models_2 x_44 x_8 x_9)
	    (models_2 (cons_0 true_0 x_44) x_8 (cons_2 (pair_1 x_8 true_0) x_9)))))
(assert (forall ((x_46 list_0) (y_8 Nat_0) (x_9 list_2) (x_8 Nat_0))
	(=>	(and (diseqNat_0 x_8 y_8)
			(models_2 x_46 x_8 x_9))
		(models_2 (cons_0 false_0 x_46) x_8 (cons_2 (pair_1 y_8 true_0) x_9)))))
(assert (forall ((x_47 list_0) (y_8 Nat_0) (x_10 Bool_0) (x_9 list_2) (x_8 Nat_0))
	(=>	(and (diseqBool_0 x_10 true_0)
			(models_2 x_47 x_8 x_9))
		(models_2 x_47 x_8 (cons_2 (pair_1 y_8 x_10) x_9)))))
(assert (forall ((x_8 Nat_0))
	(models_2 nil_0 x_8 nil_2)))
(declare-fun elem_0 (Bool_0 Nat_0 list_1) Bool)
(assert (forall ((xs_3 list_1) (x_11 Nat_0))
	(elem_0 true_0 x_11 (cons_1 x_11 xs_3))))
(assert (forall ((x_51 Bool_0) (z_4 Nat_0) (xs_3 list_1) (x_11 Nat_0))
	(=>	(and (diseqNat_0 z_4 x_11)
			(elem_0 x_51 x_11 xs_3))
		(elem_0 x_51 x_11 (cons_1 z_4 xs_3)))))
(assert (forall ((x_11 Nat_0))
	(elem_0 false_0 x_11 nil_1)))
(declare-fun okay_1 (Bool_0 list_2) Bool)
(assert (forall ((x_100 Bool_0) (x_101 Bool_0) (x_55 list_1) (x_56 Bool_0) (x_57 Bool_0) (z_5 Nat_0) (c_0 Bool_0) (m_0 list_2))
	(=>	(and (okay_0 x_55 m_0)
			(elem_0 x_56 z_5 x_55)
			(okay_1 x_57 m_0)
			(not_1 x_100 x_56)
			(and_0 x_101 x_100 x_57))
		(okay_1 x_101 (cons_2 (pair_1 z_5 c_0) m_0)))))
(assert (okay_1 true_0 nil_2))
(declare-fun formula_0 (Bool_0 list_3) Bool)
(assert (forall ((x_102 Bool_0) (x_60 Bool_0) (x_61 Bool_0) (y_11 list_2) (xs_4 list_3))
	(=>	(and (okay_1 x_60 y_11)
			(formula_0 x_61 xs_4)
			(and_0 x_102 x_60 x_61))
		(formula_0 x_102 (cons_3 y_11 xs_4)))))
(assert (formula_0 true_0 nil_3))
(declare-fun x_14 (list_3 list_3 list_3) Bool)
(assert (forall ((x_64 list_3) (z_6 list_2) (xs_5 list_3) (y_12 list_3))
	(=> (x_14 x_64 xs_5 y_12)
	    (x_14 (cons_3 z_6 x_64) (cons_3 z_6 xs_5) y_12))))
(assert (forall ((x_65 list_3))
	(x_14 x_65 nil_3 x_65)))
(declare-fun models_3 (list_3 Form_0 list_2) Bool)
(declare-fun models_4 (list_3 Form_0 list_3) Bool)
(declare-fun models_5 (list_3 list_3 Form_0 list_3) Bool)
(assert (forall ((x_69 list_2) (x_66 list_0) (x_67 Bool_0) (x_21 Nat_0) (y_15 list_2))
	(=>	(and (diseqBool_0 x_67 true_0)
			(models_0 x_69 x_21 y_15)
			(models_1 x_66 x_21 y_15)
			(or_0 x_67 x_66))
		(models_3 (cons_3 (cons_2 (pair_1 x_21 true_0) x_69) nil_3) (Var_0 x_21) y_15))))
(assert (forall ((x_70 list_0) (x_21 Nat_0) (y_15 list_2))
	(=>	(and (models_1 x_70 x_21 y_15)
			(or_0 true_0 x_70))
		(models_3 nil_3 (Var_0 x_21) y_15))))
(assert (forall ((x_76 list_2) (x_73 list_0) (x_74 Bool_0) (x_20 Nat_0) (y_15 list_2))
	(=>	(and (diseqBool_0 x_74 true_0)
			(models_0 x_76 x_20 y_15)
			(models_2 x_73 x_20 y_15)
			(or_0 x_74 x_73))
		(models_3 (cons_3 (cons_2 (pair_1 x_20 false_0) x_76) nil_3) (Not_0 (Var_0 x_20)) y_15))))
(assert (forall ((x_77 list_0) (x_20 Nat_0) (y_15 list_2))
	(=>	(and (models_2 x_77 x_20 y_15)
			(or_0 true_0 x_77))
		(models_3 nil_3 (Not_0 (Var_0 x_20)) y_15))))
(assert (forall ((x_80 list_3) (p_1 Form_0) (y_15 list_2))
	(=> (models_3 x_80 p_1 y_15)
	    (models_3 x_80 (Not_0 (Not_0 p_1)) y_15))))
(assert (forall ((x_82 list_3) (x_83 list_3) (x_84 list_3) (r_0 Form_0) (q_3 Form_0) (y_15 list_2))
	(=>	(and (models_3 x_83 (Not_0 r_0) y_15)
			(models_3 x_84 (x_0 r_0 (Not_0 q_3)) y_15)
			(x_14 x_82 x_83 x_84))
		(models_3 x_82 (Not_0 (x_0 r_0 q_3)) y_15))))
(assert (forall ((x_86 list_3) (x_87 list_3) (p_0 Form_0) (q_2 Form_0) (y_15 list_2))
	(=>	(and (models_3 x_87 p_0 y_15)
			(models_4 x_86 q_2 x_87))
		(models_3 x_86 (x_0 p_0 q_2) y_15))))
(assert (forall ((x_89 list_3) (x_90 list_3) (y_16 list_2) (z_8 list_3) (q_4 Form_0))
	(=>	(and (models_3 x_90 q_4 y_16)
			(models_5 x_89 z_8 q_4 x_90))
		(models_4 x_89 q_4 (cons_3 y_16 z_8)))))
(assert (forall ((q_4 Form_0))
	(models_4 nil_3 q_4 nil_3)))
(assert (forall ((x_94 list_3) (z_9 list_2) (x_24 list_3) (x_23 list_3) (q_5 Form_0))
	(=> (models_5 x_94 x_23 q_5 x_24)
	    (models_5 (cons_3 z_9 x_94) x_23 q_5 (cons_3 z_9 x_24)))))
(assert (forall ((x_95 list_3) (x_23 list_3) (q_5 Form_0))
	(=> (models_4 x_95 q_5 x_23)
	    (models_5 x_95 x_23 q_5 nil_3))))
(assert (forall ((x_97 list_3) (x_98 Bool_0) (p_2 Form_0))
	(=>	(and (diseqBool_0 x_98 true_0)
			(models_3 x_97 p_2 nil_2)
			(formula_0 x_98 x_97))
		false)))
(check-sat)
