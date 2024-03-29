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
(declare-datatypes ((Token_0 0)) (((A_0 ) (B_0 ) (C_0 ) (D_0 ) (ESC_0 ) (P_0 ) (Q_0 ) (R_0 ))))
(declare-fun diseqToken_0 (Token_0 Token_0) Bool)
(declare-fun isA_0 (Token_0) Bool)
(declare-fun isB_0 (Token_0) Bool)
(declare-fun isC_0 (Token_0) Bool)
(declare-fun isD_0 (Token_0) Bool)
(declare-fun isESC_0 (Token_0) Bool)
(declare-fun isP_0 (Token_0) Bool)
(declare-fun isQ_0 (Token_0) Bool)
(declare-fun isR_0 (Token_0) Bool)
(assert (isA_0 A_0))
(assert (isB_0 B_0))
(assert (isC_0 C_0))
(assert (isD_0 D_0))
(assert (isESC_0 ESC_0))
(assert (isP_0 P_0))
(assert (isQ_0 Q_0))
(assert (isR_0 R_0))
(assert (diseqToken_0 A_0 B_0))
(assert (diseqToken_0 A_0 C_0))
(assert (diseqToken_0 A_0 D_0))
(assert (diseqToken_0 A_0 ESC_0))
(assert (diseqToken_0 A_0 P_0))
(assert (diseqToken_0 A_0 Q_0))
(assert (diseqToken_0 A_0 R_0))
(assert (diseqToken_0 B_0 A_0))
(assert (diseqToken_0 C_0 A_0))
(assert (diseqToken_0 D_0 A_0))
(assert (diseqToken_0 ESC_0 A_0))
(assert (diseqToken_0 P_0 A_0))
(assert (diseqToken_0 Q_0 A_0))
(assert (diseqToken_0 R_0 A_0))
(assert (diseqToken_0 B_0 C_0))
(assert (diseqToken_0 B_0 D_0))
(assert (diseqToken_0 B_0 ESC_0))
(assert (diseqToken_0 B_0 P_0))
(assert (diseqToken_0 B_0 Q_0))
(assert (diseqToken_0 B_0 R_0))
(assert (diseqToken_0 C_0 B_0))
(assert (diseqToken_0 D_0 B_0))
(assert (diseqToken_0 ESC_0 B_0))
(assert (diseqToken_0 P_0 B_0))
(assert (diseqToken_0 Q_0 B_0))
(assert (diseqToken_0 R_0 B_0))
(assert (diseqToken_0 C_0 D_0))
(assert (diseqToken_0 C_0 ESC_0))
(assert (diseqToken_0 C_0 P_0))
(assert (diseqToken_0 C_0 Q_0))
(assert (diseqToken_0 C_0 R_0))
(assert (diseqToken_0 D_0 C_0))
(assert (diseqToken_0 ESC_0 C_0))
(assert (diseqToken_0 P_0 C_0))
(assert (diseqToken_0 Q_0 C_0))
(assert (diseqToken_0 R_0 C_0))
(assert (diseqToken_0 D_0 ESC_0))
(assert (diseqToken_0 D_0 P_0))
(assert (diseqToken_0 D_0 Q_0))
(assert (diseqToken_0 D_0 R_0))
(assert (diseqToken_0 ESC_0 D_0))
(assert (diseqToken_0 P_0 D_0))
(assert (diseqToken_0 Q_0 D_0))
(assert (diseqToken_0 R_0 D_0))
(assert (diseqToken_0 ESC_0 P_0))
(assert (diseqToken_0 ESC_0 Q_0))
(assert (diseqToken_0 ESC_0 R_0))
(assert (diseqToken_0 P_0 ESC_0))
(assert (diseqToken_0 Q_0 ESC_0))
(assert (diseqToken_0 R_0 ESC_0))
(assert (diseqToken_0 P_0 Q_0))
(assert (diseqToken_0 P_0 R_0))
(assert (diseqToken_0 Q_0 P_0))
(assert (diseqToken_0 R_0 P_0))
(assert (diseqToken_0 Q_0 R_0))
(assert (diseqToken_0 R_0 Q_0))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Token_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Token_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_73 Token_0) (x_74 list_0))
	(head_1 x_73 (cons_0 x_73 x_74))))
(assert (forall ((x_73 Token_0) (x_74 list_0))
	(tail_1 x_74 (cons_0 x_73 x_74))))
(assert (isnil_0 nil_0))
(assert (forall ((x_76 Token_0) (x_77 list_0))
	(iscons_0 (cons_0 x_76 x_77))))
(assert (forall ((x_78 Token_0) (x_79 list_0))
	(diseqlist_0 nil_0 (cons_0 x_78 x_79))))
(assert (forall ((x_80 Token_0) (x_81 list_0))
	(diseqlist_0 (cons_0 x_80 x_81) nil_0)))
(assert (forall ((x_82 Token_0) (x_83 list_0) (x_84 Token_0) (x_85 list_0))
	(=> (diseqToken_0 x_82 x_84)
	    (diseqlist_0 (cons_0 x_82 x_83) (cons_0 x_84 x_85)))))
(assert (forall ((x_82 Token_0) (x_83 list_0) (x_84 Token_0) (x_85 list_0))
	(=> (diseqlist_0 x_83 x_85)
	    (diseqlist_0 (cons_0 x_82 x_83) (cons_0 x_84 x_85)))))
(declare-fun isSpecial_0 (Bool_0 Token_0) Bool)
(assert (isSpecial_0 true_0 R_0))
(assert (isSpecial_0 true_0 Q_0))
(assert (isSpecial_0 true_0 P_0))
(assert (isSpecial_0 true_0 ESC_0))
(assert (forall ((x_1 Token_0))
	(isSpecial_0 false_0 A_0)))
(assert (forall ((x_1 Token_0))
	(isSpecial_0 false_0 B_0)))
(assert (forall ((x_1 Token_0))
	(isSpecial_0 false_0 C_0)))
(assert (forall ((x_1 Token_0))
	(isSpecial_0 false_0 D_0)))
(declare-fun ok_0 (Bool_0 Token_0) Bool)
(assert (ok_0 true_0 ESC_0))
(assert (forall ((x_17 Bool_0) (x_18 Bool_0) (x_3 Token_0))
	(=>	(and (isSpecial_0 x_18 A_0)
			(not_0 x_17 x_18))
		(ok_0 x_17 A_0))))
(assert (forall ((x_19 Bool_0) (x_20 Bool_0) (x_3 Token_0))
	(=>	(and (isSpecial_0 x_20 B_0)
			(not_0 x_19 x_20))
		(ok_0 x_19 B_0))))
(assert (forall ((x_21 Bool_0) (x_22 Bool_0) (x_3 Token_0))
	(=>	(and (isSpecial_0 x_22 C_0)
			(not_0 x_21 x_22))
		(ok_0 x_21 C_0))))
(assert (forall ((x_23 Bool_0) (x_24 Bool_0) (x_3 Token_0))
	(=>	(and (isSpecial_0 x_24 D_0)
			(not_0 x_23 x_24))
		(ok_0 x_23 D_0))))
(assert (forall ((x_25 Bool_0) (x_26 Bool_0) (x_3 Token_0))
	(=>	(and (isSpecial_0 x_26 P_0)
			(not_0 x_25 x_26))
		(ok_0 x_25 P_0))))
(assert (forall ((x_27 Bool_0) (x_28 Bool_0) (x_3 Token_0))
	(=>	(and (isSpecial_0 x_28 Q_0)
			(not_0 x_27 x_28))
		(ok_0 x_27 Q_0))))
(assert (forall ((x_29 Bool_0) (x_30 Bool_0) (x_3 Token_0))
	(=>	(and (isSpecial_0 x_30 R_0)
			(not_0 x_29 x_30))
		(ok_0 x_29 R_0))))
(declare-fun formula_0 (Bool_0 list_0) Bool)
(assert (forall ((x_31 Bool_0) (x_32 Bool_0) (x_33 Bool_0) (y_0 Token_0) (xs_0 list_0))
	(=>	(and (ok_0 x_32 y_0)
			(formula_0 x_33 xs_0)
			(and_0 x_31 x_32 x_33))
		(formula_0 x_31 (cons_0 y_0 xs_0)))))
(assert (formula_0 true_0 nil_0))
(declare-fun code_0 (Token_0 Token_0) Bool)
(assert (code_0 C_0 R_0))
(assert (code_0 B_0 Q_0))
(assert (code_0 A_0 P_0))
(assert (code_0 ESC_0 ESC_0))
(assert (forall ((x_6 Token_0))
	(code_0 A_0 A_0)))
(assert (forall ((x_6 Token_0))
	(code_0 B_0 B_0)))
(assert (forall ((x_6 Token_0))
	(code_0 C_0 C_0)))
(assert (forall ((x_6 Token_0))
	(code_0 D_0 D_0)))
(declare-fun escape_0 (list_0 list_0) Bool)
(assert (forall ((x_45 Token_0) (x_46 list_0) (y_1 Token_0) (xs_1 list_0))
	(=>	(and (code_0 x_45 y_1)
			(escape_0 x_46 xs_1)
			(isSpecial_0 true_0 y_1))
		(escape_0 (cons_0 ESC_0 (cons_0 x_45 x_46)) (cons_0 y_1 xs_1)))))
(assert (forall ((x_49 list_0) (x_47 Bool_0) (y_1 Token_0) (xs_1 list_0))
	(=>	(and (diseqBool_0 x_47 true_0)
			(escape_0 x_49 xs_1)
			(isSpecial_0 x_47 y_1))
		(escape_0 (cons_0 y_1 x_49) (cons_0 y_1 xs_1)))))
(assert (escape_0 nil_0 nil_0))
(assert (forall ((x_51 list_0) (x_52 Bool_0) (xs_2 list_0))
	(=>	(and (diseqBool_0 x_52 true_0)
			(escape_0 x_51 xs_2)
			(formula_0 x_52 x_51))
		false)))
(check-sat)
