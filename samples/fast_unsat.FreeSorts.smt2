(set-logic UF)
(declare-sort Nat_2 0)
(declare-fun Z_5 () Nat_2)
(declare-fun S_1 (Nat_2) Nat_2)
(declare-sort list_0 0)
(declare-fun nil_0 () list_0)
(declare-fun cons_0 (Nat_2 list_0) list_0)
(declare-sort E_0 0)
(declare-fun N_0 (Nat_2) E_0)
(declare-fun Add_1 (E_0 E_0) E_0)
(declare-fun Mul_0 (E_0 E_0) E_0)
(declare-fun Eq_0 (E_0 E_0) E_0)
(declare-fun V_0 (Nat_2) E_0)
(declare-sort P_0 0)
(declare-sort list_1 0)
(declare-fun Print_0 (E_0) P_0)
(declare-fun x_20 (Nat_2 E_0) P_0)
(declare-fun While_0 (E_0 list_1) P_0)
(declare-fun If_0 (E_0 list_1 list_1) P_0)
(declare-fun nil_1 () list_1)
(declare-fun cons_1 (P_0 list_1) list_1)
(declare-fun diseqNat_2 (Nat_2 Nat_2) Bool)
(declare-fun add_2 (Nat_2 Nat_2 Nat_2) Bool)
(declare-fun minus_1 (Nat_2 Nat_2 Nat_2) Bool)
(declare-fun mult_1 (Nat_2 Nat_2 Nat_2) Bool)
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun store_0 (list_0 list_0 Nat_2 Nat_2) Bool)
(declare-fun fetch_0 (Nat_2 list_0 Nat_2) Bool)
(declare-fun eval_0 (Nat_2 list_0 E_0) Bool)
(declare-fun x_21 (list_1 list_1 list_1) Bool)
(declare-fun opti_0 (P_0 P_0) Bool)
(declare-fun run_0 (list_0 list_0 list_1) Bool)
(assert (forall ((x_22 Nat_2))
	(diseqNat_2 Z_5 (S_1 x_22))))
(assert (forall ((x_23 Nat_2))
	(diseqNat_2 (S_1 x_23) Z_5)))
(assert (forall ((x_24 Nat_2) (x_25 Nat_2))
	(=> (diseqNat_2 x_24 x_25) (diseqNat_2 (S_1 x_24) (S_1 x_25)))))
(assert (forall ((y_1 Nat_2))
	(add_2 y_1 Z_5 y_1)))
(assert (forall ((r_1 Nat_2) (x_26 Nat_2) (y_2 Nat_2))
	(=> (add_2 r_1 x_26 y_2) (add_2 (S_1 r_1) (S_1 x_26) y_2))))
(assert (forall ((y_3 Nat_2))
	(minus_1 Z_5 Z_5 y_3)))
(assert (forall ((r_2 Nat_2) (x_27 Nat_2) (y_4 Nat_2))
	(=> (minus_1 r_2 x_27 y_4) (minus_1 (S_1 r_2) (S_1 x_27) y_4))))
(assert (forall ((y_5 Nat_2))
	(mult_1 Z_5 Z_5 y_5)))
(assert (forall ((r_3 Nat_2) (x_28 Nat_2) (y_6 Nat_2) (z_6 Nat_2))
	(=> (and (mult_1 r_3 x_28 y_6) (add_2 z_6 r_3 y_6)) (mult_1 z_6 (S_1 x_28) y_6))))
(assert (forall ((x_29 Nat_2) (x_30 list_0))
	(diseqlist_0 nil_0 (cons_0 x_29 x_30))))
(assert (forall ((x_31 Nat_2) (x_32 list_0))
	(diseqlist_0 (cons_0 x_31 x_32) nil_0)))
(assert (forall ((x_33 Nat_2) (x_34 list_0) (x_35 Nat_2) (x_36 list_0))
	(=> (diseqNat_2 x_33 x_35) (diseqlist_0 (cons_0 x_33 x_34) (cons_0 x_35 x_36)))))
(assert (forall ((x_37 Nat_2) (x_38 list_0) (x_39 Nat_2) (x_40 list_0))
	(=> (diseqlist_0 x_38 x_40) (diseqlist_0 (cons_0 x_37 x_38) (cons_0 x_39 x_40)))))
(assert (forall ((n_1 Nat_2) (st_0 list_0) (z_7 Nat_2))
	(store_0 (cons_0 z_7 st_0) (cons_0 n_1 st_0) Z_5 z_7)))
(assert (forall ((x_41 Nat_2) (x_42 list_0) (n_2 Nat_2) (st_1 list_0) (y_7 Nat_2) (z_8 Nat_2))
	(=> (and (diseqNat_2 y_7 Z_5) (store_0 x_42 st_1 x_41 z_8) (minus_1 x_41 y_7 (S_1 Z_5))) (store_0 (cons_0 n_2 x_42) (cons_0 n_2 st_1) y_7 z_8))))
(assert (forall ((z_9 Nat_2))
	(store_0 (cons_0 z_9 nil_0) nil_0 Z_5 z_9)))
(assert (forall ((x_43 Nat_2) (x_44 list_0) (y_8 Nat_2) (z_10 Nat_2))
	(=> (and (diseqNat_2 y_8 Z_5) (store_0 x_44 nil_0 x_43 z_10) (minus_1 x_43 y_8 (S_1 Z_5))) (store_0 (cons_0 Z_5 x_44) nil_0 y_8 z_10))))
(assert (forall ((n_3 Nat_2) (st_2 list_0))
	(fetch_0 n_3 (cons_0 n_3 st_2) Z_5)))
(assert (forall ((x_45 Nat_2) (x_46 Nat_2) (n_4 Nat_2) (st_3 list_0) (y_9 Nat_2))
	(=> (and (diseqNat_2 y_9 Z_5) (fetch_0 x_46 st_3 x_45) (minus_1 x_45 y_9 (S_1 Z_5))) (fetch_0 x_46 (cons_0 n_4 st_3) y_9))))
(assert (forall ((y_10 Nat_2))
	(fetch_0 Z_5 nil_0 y_10)))
(assert (forall ((x_47 Nat_2) (z_11 Nat_2) (x_48 list_0))
	(=> (fetch_0 x_47 x_48 z_11) (eval_0 x_47 x_48 (V_0 z_11)))))
(assert (forall ((x_49 Nat_2) (a_0 E_0) (b_0 E_0) (x_50 list_0))
	(=> (and (eval_0 x_49 x_50 a_0) (eval_0 x_49 x_50 b_0)) (eval_0 (S_1 Z_5) x_50 (Eq_0 a_0 b_0)))))
(assert (forall ((x_51 Nat_2) (x_52 Nat_2) (a_1 E_0) (b_1 E_0) (x_53 list_0))
	(=> (and (diseqNat_2 x_51 x_52) (eval_0 x_51 x_53 a_1) (eval_0 x_52 x_53 b_1)) (eval_0 Z_5 x_53 (Eq_0 a_1 b_1)))))
(assert (forall ((x_54 Nat_2) (x_55 Nat_2) (x_56 Nat_2) (c_0 E_0) (b_2 E_0) (x_57 list_0))
	(=> (and (eval_0 x_55 x_57 c_0) (eval_0 x_56 x_57 b_2) (mult_1 x_54 x_55 x_56)) (eval_0 x_54 x_57 (Mul_0 c_0 b_2)))))
(assert (forall ((x_58 Nat_2) (x_59 Nat_2) (x_60 Nat_2) (a_2 E_0) (b_3 E_0) (x_61 list_0))
	(=> (and (eval_0 x_59 x_61 a_2) (eval_0 x_60 x_61 b_3) (add_2 x_58 x_59 x_60)) (eval_0 x_58 x_61 (Add_1 a_2 b_3)))))
(assert (forall ((n_5 Nat_2) (x_62 list_0))
	(eval_0 n_5 x_62 (N_0 n_5))))
(assert (forall ((x_63 list_1) (z_12 P_0) (xs_0 list_1) (y_11 list_1))
	(=> (x_21 x_63 xs_0 y_11) (x_21 (cons_1 z_12 x_63) (cons_1 z_12 xs_0) y_11))))
(assert (forall ((x_64 list_1))
	(x_21 x_64 nil_1 x_64)))
(assert (forall ((c_1 E_0) (q_0 list_1) (r_4 list_1))
	(opti_0 (If_0 c_1 r_4 q_0) (If_0 c_1 q_0 r_4))))
(assert (forall ((x_65 list_1) (e_1 E_0) (p_1 list_1))
	(=> (x_21 x_65 p_1 p_1) (opti_0 (While_0 e_1 x_65) (While_0 e_1 p_1)))))
(assert (forall ((x_66 P_0) (x_67 E_0))
	(opti_0 (Print_0 x_67) (Print_0 x_67))))
(assert (forall ((x_68 P_0) (x_69 Nat_2) (x_70 E_0))
	(opti_0 (x_20 x_69 x_70) (x_20 x_69 x_70))))
(assert (forall ((x_71 list_0) (x_72 list_1) (e_2 E_0) (q_1 list_1) (q_2 list_1) (r_5 list_1) (x_73 list_0))
	(=> (and (x_21 x_72 q_2 r_5) (run_0 x_71 x_73 x_72) (eval_0 Z_5 x_73 e_2)) (run_0 x_71 x_73 (cons_1 (If_0 e_2 q_1 q_2) r_5)))))
(assert (forall ((x_74 list_0) (x_75 list_1) (x_76 Nat_2) (e_3 E_0) (q_3 list_1) (q_4 list_1) (r_6 list_1) (x_77 list_0))
	(=> (and (diseqNat_2 x_76 Z_5) (x_21 x_75 q_3 r_6) (run_0 x_74 x_77 x_75) (eval_0 x_76 x_77 e_3)) (run_0 x_74 x_77 (cons_1 (If_0 e_3 q_3 q_4) r_6)))))
(assert (forall ((x_78 list_0) (x_79 list_1) (e_4 E_0) (p_2 list_1) (r_7 list_1) (x_80 list_0))
	(=> (and (x_21 x_79 p_2 (cons_1 (While_0 e_4 p_2) nil_1)) (run_0 x_78 x_80 (cons_1 (If_0 e_4 x_79 nil_1) r_7))) (run_0 x_78 x_80 (cons_1 (While_0 e_4 p_2) r_7)))))
(assert (forall ((x_81 list_0) (x_82 Nat_2) (x_83 list_0) (x_84 Nat_2) (e_5 E_0) (r_8 list_1) (x_85 list_0))
	(=> (and (eval_0 x_82 x_85 e_5) (store_0 x_83 x_85 x_84 x_82) (run_0 x_81 x_83 r_8)) (run_0 x_81 x_85 (cons_1 (x_20 x_84 e_5) r_8)))))
(assert (forall ((x_86 Nat_2) (x_87 list_0) (e_6 E_0) (r_9 list_1) (x_88 list_0))
	(=> (and (eval_0 x_86 x_88 e_6) (run_0 x_87 x_88 r_9)) (run_0 (cons_0 x_86 x_87) x_88 (cons_1 (Print_0 e_6) r_9)))))
(assert (forall ((x_89 list_0))
	(run_0 nil_0 x_89 nil_1)))
(assert (forall ((x_90 list_0) (x_91 P_0) (x_92 list_0) (p_3 P_0))
	(=> (and (diseqlist_0 x_90 x_92) (run_0 x_90 nil_0 (cons_1 p_3 nil_1)) (opti_0 x_91 p_3) (run_0 x_92 nil_0 (cons_1 x_91 nil_1))) false)))
(check-sat)
(get-model)