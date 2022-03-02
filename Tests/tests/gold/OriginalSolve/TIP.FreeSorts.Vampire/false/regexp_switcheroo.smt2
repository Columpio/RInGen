9
25636
300
UNSAT
tff(type_def_5, type, 'Bool_0()': $tType).
tff(type_def_6, type, 'T_0()': $tType).
tff(type_def_7, type, 'list_0()': $tType).
tff(type_def_8, type, 'R_0()': $tType).
tff(func_def_0, type, false_0: 'Bool_0()').
tff(func_def_1, type, true_0: 'Bool_0()').
tff(func_def_2, type, 'A_0': 'T_0()').
tff(func_def_3, type, 'B_0': 'T_0()').
tff(func_def_4, type, 'C_0': 'T_0()').
tff(func_def_5, type, nil_0: 'list_0()').
tff(func_def_6, type, cons_0: ('T_0()' * 'list_0()') > 'list_0()').
tff(func_def_7, type, 'Nil_1': 'R_0()').
tff(func_def_8, type, 'Eps_0': 'R_0()').
tff(func_def_9, type, 'Atom_0': ('T_0()') > 'R_0()').
tff(func_def_10, type, x_0: ('R_0()' * 'R_0()') > 'R_0()').
tff(func_def_11, type, x_1: ('R_0()' * 'R_0()') > 'R_0()').
tff(func_def_12, type, 'Star_0': ('R_0()') > 'R_0()').
tff(pred_def_1, type, diseqBool_0: ('Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_2, type, isfalse_1: ('Bool_0()') > $o).
tff(pred_def_3, type, istrue_1: ('Bool_0()') > $o).
tff(pred_def_4, type, and_0: ('Bool_0()' * 'Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_5, type, or_0: ('Bool_0()' * 'Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_6, type, hence_0: ('Bool_0()' * 'Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_7, type, not_0: ('Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_8, type, diseqT_0: ('T_0()' * 'T_0()') > $o).
tff(pred_def_9, type, isA_0: ('T_0()') > $o).
tff(pred_def_10, type, isB_0: ('T_0()') > $o).
tff(pred_def_11, type, isC_0: ('T_0()') > $o).
tff(pred_def_12, type, diseqlist_0: ('list_0()' * 'list_0()') > $o).
tff(pred_def_13, type, head_1: ('T_0()' * 'list_0()') > $o).
tff(pred_def_14, type, tail_1: ('list_0()' * 'list_0()') > $o).
tff(pred_def_15, type, isnil_0: ('list_0()') > $o).
tff(pred_def_16, type, iscons_0: ('list_0()') > $o).
tff(pred_def_17, type, diseqR_0: ('R_0()' * 'R_0()') > $o).
tff(pred_def_18, type, projAtom_1: ('T_0()' * 'R_0()') > $o).
tff(pred_def_19, type, proj_4: ('R_0()' * 'R_0()') > $o).
tff(pred_def_20, type, proj_5: ('R_0()' * 'R_0()') > $o).
tff(pred_def_21, type, proj_6: ('R_0()' * 'R_0()') > $o).
tff(pred_def_22, type, proj_7: ('R_0()' * 'R_0()') > $o).
tff(pred_def_23, type, projStar_1: ('R_0()' * 'R_0()') > $o).
tff(pred_def_24, type, isNil_1: ('R_0()') > $o).
tff(pred_def_25, type, isEps_0: ('R_0()') > $o).
tff(pred_def_26, type, isAtom_0: ('R_0()') > $o).
tff(pred_def_27, type, isx_0: ('R_0()') > $o).
tff(pred_def_28, type, isx_1: ('R_0()') > $o).
tff(pred_def_29, type, isStar_0: ('R_0()') > $o).
tff(pred_def_30, type, eps_1: ('Bool_0()' * 'R_0()') > $o).
tff(pred_def_31, type, step_0: ('R_0()' * 'R_0()' * 'T_0()') > $o).
tff(pred_def_32, type, rec_0: ('Bool_0()' * 'R_0()' * 'list_0()') > $o).
tff(pred_def_33, type, sP0: ('R_0()') > $o).
tff(pred_def_34, type, sP1: ('R_0()' * 'Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_35, type, sP2: ('Bool_0()' * 'Bool_0()' * 'R_0()') > $o).
tff(f13681,plain,(
  $false),
  inference(unit_resulting_resolution,[],[f178,f5491,f3053,f266])).
tff(f266,plain,(
  ( ! [X4 : 'R_0()',X2 : 'Bool_0()',X0 : 'list_0()',X3 : 'R_0()',X1 : 'Bool_0()'] : (~rec_0(X2,x_0(X4,X3),X0) | ~diseqBool_0(X2,X1) | ~rec_0(X1,x_1(X4,X3),X0)) )),
  inference(cnf_transformation,[],[f163])).
tff(f163,plain,(
  ! [X0 : 'list_0()',X1 : 'Bool_0()',X2 : 'Bool_0()',X3 : 'R_0()',X4 : 'R_0()'] : (~diseqBool_0(X2,X1) | ~rec_0(X2,x_0(X4,X3),X0) | ~rec_0(X1,x_1(X4,X3),X0))),
  inference(ennf_transformation,[],[f139])).
tff(f139,plain,(
  ! [X0 : 'list_0()',X1 : 'Bool_0()',X2 : 'Bool_0()',X3 : 'R_0()',X4 : 'R_0()'] : ~(diseqBool_0(X2,X1) & rec_0(X2,x_0(X4,X3),X0) & rec_0(X1,x_1(X4,X3),X0))),
  inference(true_and_false_elimination,[],[f138])).
tff(f138,plain,(
  ! [X0 : 'list_0()',X1 : 'Bool_0()',X2 : 'Bool_0()',X3 : 'R_0()',X4 : 'R_0()'] : ((diseqBool_0(X2,X1) & rec_0(X2,x_0(X4,X3),X0) & rec_0(X1,x_1(X4,X3),X0)) => $false)),
  inference(rectify,[],[f100])).
tff(f100,axiom,(
  ! [X4 : 'list_0()',X1 : 'Bool_0()',X0 : 'Bool_0()',X3 : 'R_0()',X2 : 'R_0()'] : ((diseqBool_0(X0,X1) & rec_0(X0,x_0(X2,X3),X4) & rec_0(X1,x_1(X2,X3),X4)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/regexp_switcheroo.smt2',unknown)).
tff(f3053,plain,(
  rec_0(true_0,x_0('Nil_1','Eps_0'),nil_0)),
  inference(unit_resulting_resolution,[],[f2979,f241])).
tff(f241,plain,(
  ( ! [X0 : 'Bool_0()',X1 : 'R_0()'] : (rec_0(X0,X1,nil_0) | ~eps_1(X0,X1)) )),
  inference(cnf_transformation,[],[f142])).
tff(f142,plain,(
  ! [X0 : 'Bool_0()',X1 : 'R_0()'] : (rec_0(X0,X1,nil_0) | ~eps_1(X0,X1))),
  inference(ennf_transformation,[],[f99])).
tff(f99,axiom,(
  ! [X0 : 'Bool_0()',X1 : 'R_0()'] : (eps_1(X0,X1) => rec_0(X0,X1,nil_0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/regexp_switcheroo.smt2',unknown)).
tff(f2979,plain,(
  eps_1(true_0,x_0('Nil_1','Eps_0'))),
  inference(unit_resulting_resolution,[],[f1828,f202,f270])).
tff(f270,plain,(
  ( ! [X2 : 'R_0()',X0 : 'Bool_0()',X3 : 'R_0()',X1 : 'Bool_0()'] : (~sP1(X3,X1,X0) | ~eps_1(X1,X2) | eps_1(X0,x_0(X2,X3))) )),
  inference(general_splitting,[],[f263,f269_D])).
tff(f269,plain,(
  ( ! [X4 : 'Bool_0()',X0 : 'Bool_0()',X3 : 'R_0()',X1 : 'Bool_0()'] : (~or_0(X0,X1,X4) | ~eps_1(X4,X3) | sP1(X3,X1,X0)) )),
  inference(cnf_transformation,[],[f269_D])).
tff(f269_D,plain,(
  ( ! [X0,X1,X3] : (( ! [X4] : (~or_0(X0,X1,X4) | ~eps_1(X4,X3)) ) <=> ~sP1(X3,X1,X0)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP1])])).
tff(f263,plain,(
  ( ! [X4 : 'Bool_0()',X2 : 'R_0()',X0 : 'Bool_0()',X3 : 'R_0()',X1 : 'Bool_0()'] : (eps_1(X0,x_0(X2,X3)) | ~eps_1(X1,X2) | ~eps_1(X4,X3) | ~or_0(X0,X1,X4)) )),
  inference(cnf_transformation,[],[f158])).
tff(f158,plain,(
  ! [X0 : 'Bool_0()',X1 : 'Bool_0()',X2 : 'R_0()',X3 : 'R_0()',X4 : 'Bool_0()'] : (eps_1(X0,x_0(X2,X3)) | ~eps_1(X1,X2) | ~eps_1(X4,X3) | ~or_0(X0,X1,X4))),
  inference(flattening,[],[f157])).
tff(f157,plain,(
  ! [X0 : 'Bool_0()',X1 : 'Bool_0()',X2 : 'R_0()',X3 : 'R_0()',X4 : 'Bool_0()'] : (eps_1(X0,x_0(X2,X3)) | (~eps_1(X1,X2) | ~eps_1(X4,X3) | ~or_0(X0,X1,X4)))),
  inference(ennf_transformation,[],[f135])).
tff(f135,plain,(
  ! [X0 : 'Bool_0()',X1 : 'Bool_0()',X2 : 'R_0()',X3 : 'R_0()',X4 : 'Bool_0()'] : ((eps_1(X1,X2) & eps_1(X4,X3) & or_0(X0,X1,X4)) => eps_1(X0,x_0(X2,X3)))),
  inference(rectify,[],[f86])).
tff(f86,axiom,(
  ! [X0 : 'Bool_0()',X1 : 'Bool_0()',X3 : 'R_0()',X4 : 'R_0()',X2 : 'Bool_0()'] : ((eps_1(X1,X3) & eps_1(X2,X4) & or_0(X0,X1,X2)) => eps_1(X0,x_0(X3,X4)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/regexp_switcheroo.smt2',unknown)).
tff(f202,plain,(
  eps_1(false_0,'Nil_1')),
  inference(cnf_transformation,[],[f101])).
tff(f101,plain,(
  eps_1(false_0,'Nil_1')),
  inference(rectify,[],[f89])).
tff(f89,axiom,(
  ! [X0 : 'R_0()'] : eps_1(false_0,'Nil_1')),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/regexp_switcheroo.smt2',unknown)).
tff(f1828,plain,(
  sP1('Eps_0',false_0,true_0)),
  inference(unit_resulting_resolution,[],[f185,f196,f269])).
tff(f196,plain,(
  or_0(true_0,false_0,true_0)),
  inference(cnf_transformation,[],[f11])).
tff(f11,axiom,(
  or_0(true_0,false_0,true_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/regexp_switcheroo.smt2',unknown)).
tff(f185,plain,(
  eps_1(true_0,'Eps_0')),
  inference(cnf_transformation,[],[f87])).
tff(f87,axiom,(
  eps_1(true_0,'Eps_0')),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/regexp_switcheroo.smt2',unknown)).
tff(f5491,plain,(
  rec_0(false_0,x_1('Nil_1','Eps_0'),nil_0)),
  inference(unit_resulting_resolution,[],[f5132,f241])).
tff(f5132,plain,(
  eps_1(false_0,x_1('Nil_1','Eps_0'))),
  inference(unit_resulting_resolution,[],[f1993,f202,f272])).
tff(f272,plain,(
  ( ! [X2 : 'Bool_0()',X0 : 'R_0()',X3 : 'Bool_0()',X1 : 'R_0()'] : (~sP2(X3,X2,X0) | ~eps_1(X3,X1) | eps_1(X2,x_1(X1,X0))) )),
  inference(general_splitting,[],[f264,f271_D])).
tff(f271,plain,(
  ( ! [X4 : 'Bool_0()',X2 : 'Bool_0()',X0 : 'R_0()',X3 : 'Bool_0()'] : (~and_0(X2,X3,X4) | ~eps_1(X4,X0) | sP2(X3,X2,X0)) )),
  inference(cnf_transformation,[],[f271_D])).
tff(f271_D,plain,(
  ( ! [X0,X2,X3] : (( ! [X4] : (~and_0(X2,X3,X4) | ~eps_1(X4,X0)) ) <=> ~sP2(X3,X2,X0)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).
tff(f264,plain,(
  ( ! [X4 : 'Bool_0()',X2 : 'Bool_0()',X0 : 'R_0()',X3 : 'Bool_0()',X1 : 'R_0()'] : (eps_1(X2,x_1(X1,X0)) | ~eps_1(X3,X1) | ~eps_1(X4,X0) | ~and_0(X2,X3,X4)) )),
  inference(cnf_transformation,[],[f160])).
tff(f160,plain,(
  ! [X0 : 'R_0()',X1 : 'R_0()',X2 : 'Bool_0()',X3 : 'Bool_0()',X4 : 'Bool_0()'] : (eps_1(X2,x_1(X1,X0)) | ~eps_1(X3,X1) | ~eps_1(X4,X0) | ~and_0(X2,X3,X4))),
  inference(flattening,[],[f159])).
tff(f159,plain,(
  ! [X0 : 'R_0()',X1 : 'R_0()',X2 : 'Bool_0()',X3 : 'Bool_0()',X4 : 'Bool_0()'] : (eps_1(X2,x_1(X1,X0)) | (~eps_1(X3,X1) | ~eps_1(X4,X0) | ~and_0(X2,X3,X4)))),
  inference(ennf_transformation,[],[f136])).
tff(f136,plain,(
  ! [X0 : 'R_0()',X1 : 'R_0()',X2 : 'Bool_0()',X3 : 'Bool_0()',X4 : 'Bool_0()'] : ((eps_1(X3,X1) & eps_1(X4,X0) & and_0(X2,X3,X4)) => eps_1(X2,x_1(X1,X0)))),
  inference(rectify,[],[f85])).
tff(f85,axiom,(
  ! [X4 : 'R_0()',X3 : 'R_0()',X0 : 'Bool_0()',X1 : 'Bool_0()',X2 : 'Bool_0()'] : ((eps_1(X1,X3) & eps_1(X2,X4) & and_0(X0,X1,X2)) => eps_1(X0,x_1(X3,X4)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/regexp_switcheroo.smt2',unknown)).
tff(f1993,plain,(
  sP2(false_0,false_0,'Eps_0')),
  inference(unit_resulting_resolution,[],[f185,f194,f271])).
tff(f194,plain,(
  and_0(false_0,false_0,true_0)),
  inference(cnf_transformation,[],[f7])).
tff(f7,axiom,(
  and_0(false_0,false_0,true_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/regexp_switcheroo.smt2',unknown)).
tff(f178,plain,(
  diseqBool_0(true_0,false_0)),
  inference(cnf_transformation,[],[f4])).
tff(f4,axiom,(
  diseqBool_0(true_0,false_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/regexp_switcheroo.smt2',unknown)).
