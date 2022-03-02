4
17560
450
UNSAT
tff(type_def_5, type, 'Bool_0()': $tType).
tff(type_def_6, type, 'Nat_0()': $tType).
tff(type_def_7, type, 'list_0()': $tType).
tff(func_def_0, type, false_0: 'Bool_0()').
tff(func_def_1, type, true_0: 'Bool_0()').
tff(func_def_2, type, 'S_0': ('Nat_0()') > 'Nat_0()').
tff(func_def_3, type, 'Z_0': 'Nat_0()').
tff(func_def_4, type, nil_0: 'list_0()').
tff(func_def_5, type, cons_0: ('Nat_0()' * 'list_0()') > 'list_0()').
tff(pred_def_1, type, diseqBool_0: ('Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_2, type, isfalse_1: ('Bool_0()') > $o).
tff(pred_def_3, type, istrue_1: ('Bool_0()') > $o).
tff(pred_def_4, type, and_0: ('Bool_0()' * 'Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_5, type, or_0: ('Bool_0()' * 'Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_6, type, hence_0: ('Bool_0()' * 'Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_7, type, not_0: ('Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_8, type, diseqNat_0: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_9, type, projS_1: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_10, type, isS_0: ('Nat_0()') > $o).
tff(pred_def_11, type, isZ_2: ('Nat_0()') > $o).
tff(pred_def_12, type, diseqlist_0: ('list_0()' * 'list_0()') > $o).
tff(pred_def_13, type, head_1: ('Nat_0()' * 'list_0()') > $o).
tff(pred_def_14, type, tail_1: ('list_0()' * 'list_0()') > $o).
tff(pred_def_15, type, isnil_0: ('list_0()') > $o).
tff(pred_def_16, type, iscons_0: ('list_0()') > $o).
tff(pred_def_17, type, length_0: ('Nat_0()' * 'list_0()') > $o).
tff(pred_def_18, type, x_1: ('Bool_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_19, type, x_4: ('list_0()' * 'list_0()' * 'list_0()') > $o).
tff(pred_def_20, type, rotate_0: ('list_0()' * 'Nat_0()' * 'list_0()') > $o).
tff(pred_def_21, type, sP0: ('list_0()') > $o).
tff(pred_def_22, type, sP1: ('list_0()' * 'Nat_0()') > $o).
tff(pred_def_23, type, sP2: ('Nat_0()' * 'list_0()') > $o).
tff(f11663,plain,(
  $false),
  inference(unit_resulting_resolution,[],[f87,f5850,f227,f250,f91,f8623,f113])).
tff(f113,plain,(
  ( ! [X0 : 'Nat_0()',X5 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~rotate_0(X3,X5,X1) | ~diseqNat_0(X5,X0) | ~rotate_0(X3,X0,X1) | ~sP0(X1) | ~sP1(X1,X0) | ~sP2(X5,X1)) )),
  inference(general_splitting,[],[f111,f112_D])).
tff(f112,plain,(
  ( ! [X2 : 'Nat_0()',X5 : 'Nat_0()',X1 : 'list_0()'] : (~x_1(true_0,X5,X2) | ~length_0(X2,X1) | sP2(X5,X1)) )),
  inference(cnf_transformation,[],[f112_D])).
tff(f112_D,plain,(
  ( ! [X1,X5] : (( ! [X2] : (~x_1(true_0,X5,X2) | ~length_0(X2,X1)) ) <=> ~sP2(X5,X1)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).
tff(f111,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X5 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~diseqNat_0(X5,X0) | ~length_0(X2,X1) | ~x_1(true_0,X5,X2) | ~rotate_0(X3,X5,X1) | ~rotate_0(X3,X0,X1) | ~sP0(X1) | ~sP1(X1,X0)) )),
  inference(general_splitting,[],[f109,f110_D])).
tff(f110,plain,(
  ( ! [X6 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'list_0()'] : (~x_1(true_0,X0,X6) | ~length_0(X6,X1) | sP1(X1,X0)) )),
  inference(cnf_transformation,[],[f110_D])).
tff(f110_D,plain,(
  ( ! [X0,X1] : (( ! [X6] : (~x_1(true_0,X0,X6) | ~length_0(X6,X1)) ) <=> ~sP1(X1,X0)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP1])])).
tff(f109,plain,(
  ( ! [X6 : 'Nat_0()',X2 : 'Nat_0()',X0 : 'Nat_0()',X5 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~diseqNat_0(X5,X0) | ~length_0(X2,X1) | ~x_1(true_0,X5,X2) | ~length_0(X6,X1) | ~x_1(true_0,X0,X6) | ~rotate_0(X3,X5,X1) | ~rotate_0(X3,X0,X1) | ~sP0(X1)) )),
  inference(general_splitting,[],[f107,f108_D])).
tff(f108,plain,(
  ( ! [X4 : 'list_0()',X1 : 'list_0()'] : (~rotate_0(X4,'S_0'('Z_0'),X1) | ~diseqlist_0(X4,X1) | sP0(X1)) )),
  inference(cnf_transformation,[],[f108_D])).
tff(f108_D,plain,(
  ( ! [X1] : (( ! [X4] : (~rotate_0(X4,'S_0'('Z_0'),X1) | ~diseqlist_0(X4,X1)) ) <=> ~sP0(X1)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP0])])).
tff(f107,plain,(
  ( ! [X6 : 'Nat_0()',X4 : 'list_0()',X2 : 'Nat_0()',X0 : 'Nat_0()',X5 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~diseqNat_0(X5,X0) | ~diseqlist_0(X4,X1) | ~length_0(X2,X1) | ~x_1(true_0,X5,X2) | ~length_0(X6,X1) | ~x_1(true_0,X0,X6) | ~rotate_0(X4,'S_0'('Z_0'),X1) | ~rotate_0(X3,X5,X1) | ~rotate_0(X3,X0,X1)) )),
  inference(cnf_transformation,[],[f63])).
tff(f63,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()',X4 : 'list_0()',X5 : 'Nat_0()',X6 : 'Nat_0()'] : (~diseqNat_0(X5,X0) | ~diseqlist_0(X4,X1) | ~length_0(X2,X1) | ~x_1(true_0,X5,X2) | ~length_0(X6,X1) | ~x_1(true_0,X0,X6) | ~rotate_0(X4,'S_0'('Z_0'),X1) | ~rotate_0(X3,X5,X1) | ~rotate_0(X3,X0,X1))),
  inference(ennf_transformation,[],[f54])).
tff(f54,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()',X4 : 'list_0()',X5 : 'Nat_0()',X6 : 'Nat_0()'] : ~(diseqNat_0(X5,X0) & diseqlist_0(X4,X1) & length_0(X2,X1) & x_1(true_0,X5,X2) & length_0(X6,X1) & x_1(true_0,X0,X6) & rotate_0(X4,'S_0'('Z_0'),X1) & rotate_0(X3,X5,X1) & rotate_0(X3,X0,X1))),
  inference(true_and_false_elimination,[],[f53])).
tff(f53,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()',X4 : 'list_0()',X5 : 'Nat_0()',X6 : 'Nat_0()'] : ((diseqNat_0(X5,X0) & diseqlist_0(X4,X1) & length_0(X2,X1) & x_1(true_0,X5,X2) & length_0(X6,X1) & x_1(true_0,X0,X6) & rotate_0(X4,'S_0'('Z_0'),X1) & rotate_0(X3,X5,X1) & rotate_0(X3,X0,X1)) => $false)),
  inference(rectify,[],[f44])).
tff(f44,axiom,(
  ! [X5 : 'Nat_0()',X6 : 'list_0()',X0 : 'Nat_0()',X3 : 'list_0()',X2 : 'list_0()',X4 : 'Nat_0()',X1 : 'Nat_0()'] : ((diseqNat_0(X4,X5) & diseqlist_0(X2,X6) & length_0(X0,X6) & x_1(true_0,X4,X0) & length_0(X1,X6) & x_1(true_0,X5,X1) & rotate_0(X2,'S_0'('Z_0'),X6) & rotate_0(X3,X4,X6) & rotate_0(X3,X5,X6)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0'.smt2',unknown)).
tff(f8623,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'Nat_0()',X1 : 'Nat_0()'] : (rotate_0(cons_0(X0,cons_0(X1,cons_0(X2,cons_0(X3,nil_0)))),'S_0'('S_0'('Z_0')),cons_0(X2,cons_0(X3,cons_0(X0,cons_0(X1,nil_0)))))) )),
  inference(unit_resulting_resolution,[],[f214,f393,f106])).
tff(f106,plain,(
  ( ! [X4 : 'list_0()',X2 : 'Nat_0()',X0 : 'list_0()',X3 : 'Nat_0()',X1 : 'list_0()'] : (~x_4(X1,X4,cons_0(X2,nil_0)) | rotate_0(X0,'S_0'(X3),cons_0(X2,X4)) | ~rotate_0(X0,X3,X1)) )),
  inference(cnf_transformation,[],[f62])).
tff(f62,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'Nat_0()',X4 : 'list_0()'] : (rotate_0(X0,'S_0'(X3),cons_0(X2,X4)) | ~x_4(X1,X4,cons_0(X2,nil_0)) | ~rotate_0(X0,X3,X1))),
  inference(flattening,[],[f61])).
tff(f61,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'Nat_0()',X4 : 'list_0()'] : (rotate_0(X0,'S_0'(X3),cons_0(X2,X4)) | (~x_4(X1,X4,cons_0(X2,nil_0)) | ~rotate_0(X0,X3,X1)))),
  inference(ennf_transformation,[],[f52])).
tff(f52,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'Nat_0()',X4 : 'list_0()'] : ((x_4(X1,X4,cons_0(X2,nil_0)) & rotate_0(X0,X3,X1)) => rotate_0(X0,'S_0'(X3),cons_0(X2,X4)))),
  inference(rectify,[],[f42])).
tff(f42,axiom,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'Nat_0()',X4 : 'Nat_0()',X3 : 'list_0()'] : ((x_4(X1,X3,cons_0(X2,nil_0)) & rotate_0(X0,X4,X1)) => rotate_0(X0,'S_0'(X4),cons_0(X2,X3)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0'.smt2',unknown)).
tff(f393,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'Nat_0()',X1 : 'Nat_0()'] : (rotate_0(cons_0(X0,cons_0(X1,cons_0(X2,cons_0(X3,nil_0)))),'S_0'('Z_0'),cons_0(X3,cons_0(X0,cons_0(X1,cons_0(X2,nil_0)))))) )),
  inference(unit_resulting_resolution,[],[f91,f214,f106])).
tff(f214,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'Nat_0()'] : (x_4(cons_0(X0,cons_0(X1,cons_0(X2,X3))),cons_0(X0,cons_0(X1,cons_0(X2,nil_0))),X3)) )),
  inference(unit_resulting_resolution,[],[f199,f105])).
tff(f105,plain,(
  ( ! [X2 : 'list_0()',X0 : 'list_0()',X3 : 'list_0()',X1 : 'Nat_0()'] : (x_4(cons_0(X1,X2),cons_0(X1,X0),X3) | ~x_4(X2,X0,X3)) )),
  inference(cnf_transformation,[],[f60])).
tff(f60,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'list_0()',X3 : 'list_0()'] : (x_4(cons_0(X1,X2),cons_0(X1,X0),X3) | ~x_4(X2,X0,X3))),
  inference(ennf_transformation,[],[f51])).
tff(f51,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'list_0()',X3 : 'list_0()'] : (x_4(X2,X0,X3) => x_4(cons_0(X1,X2),cons_0(X1,X0),X3))),
  inference(rectify,[],[f39])).
tff(f39,axiom,(
  ! [X2 : 'list_0()',X1 : 'Nat_0()',X0 : 'list_0()',X3 : 'list_0()'] : (x_4(X0,X2,X3) => x_4(cons_0(X1,X0),cons_0(X1,X2),X3))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0'.smt2',unknown)).
tff(f199,plain,(
  ( ! [X2 : 'list_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (x_4(cons_0(X0,cons_0(X1,X2)),cons_0(X0,cons_0(X1,nil_0)),X2)) )),
  inference(unit_resulting_resolution,[],[f198,f105])).
tff(f198,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'list_0()'] : (x_4(cons_0(X0,X1),cons_0(X0,nil_0),X1)) )),
  inference(unit_resulting_resolution,[],[f90,f105])).
tff(f90,plain,(
  ( ! [X0 : 'list_0()'] : (x_4(X0,nil_0,X0)) )),
  inference(cnf_transformation,[],[f40])).
tff(f40,axiom,(
  ! [X0 : 'list_0()'] : x_4(X0,nil_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0'.smt2',unknown)).
tff(f91,plain,(
  ( ! [X0 : 'list_0()'] : (rotate_0(X0,'Z_0',X0)) )),
  inference(cnf_transformation,[],[f41])).
tff(f41,axiom,(
  ! [X0 : 'list_0()'] : rotate_0(X0,'Z_0',X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0'.smt2',unknown)).
tff(f250,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'Nat_0()',X1 : 'Nat_0()'] : (sP1(cons_0(X0,cons_0(X1,cons_0(X2,cons_0(X3,nil_0)))),'S_0'('S_0'('Z_0')))) )),
  inference(unit_resulting_resolution,[],[f122,f196])).
tff(f196,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'list_0()'] : (sP1(cons_0(X0,X1),'S_0'('S_0'('Z_0'))) | ~length_0('S_0'('S_0'(X2)),X1)) )),
  inference(resolution,[],[f150,f101])).
tff(f101,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'list_0()',X1 : 'Nat_0()'] : (length_0('S_0'(X1),cons_0(X2,X0)) | ~length_0(X1,X0)) )),
  inference(cnf_transformation,[],[f56])).
tff(f56,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (length_0('S_0'(X1),cons_0(X2,X0)) | ~length_0(X1,X0))),
  inference(ennf_transformation,[],[f47])).
tff(f47,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (length_0(X1,X0) => length_0('S_0'(X1),cons_0(X2,X0)))),
  inference(rectify,[],[f33])).
tff(f33,axiom,(
  ! [X2 : 'list_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (length_0(X0,X2) => length_0('S_0'(X0),cons_0(X1,X2)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0'.smt2',unknown)).
tff(f150,plain,(
  ( ! [X4 : 'Nat_0()',X5 : 'list_0()'] : (~length_0('S_0'('S_0'('S_0'(X4))),X5) | sP1(X5,'S_0'('S_0'('Z_0')))) )),
  inference(resolution,[],[f110,f128])).
tff(f128,plain,(
  ( ! [X0 : 'Nat_0()'] : (x_1(true_0,'S_0'('S_0'('Z_0')),'S_0'('S_0'('S_0'(X0))))) )),
  inference(unit_resulting_resolution,[],[f125,f102])).
tff(f102,plain,(
  ( ! [X2 : 'Bool_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (x_1(X2,'S_0'(X0),'S_0'(X1)) | ~x_1(X2,X0,X1)) )),
  inference(cnf_transformation,[],[f57])).
tff(f57,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Bool_0()'] : (x_1(X2,'S_0'(X0),'S_0'(X1)) | ~x_1(X2,X0,X1))),
  inference(ennf_transformation,[],[f48])).
tff(f48,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Bool_0()'] : (x_1(X2,X0,X1) => x_1(X2,'S_0'(X0),'S_0'(X1)))),
  inference(rectify,[],[f38])).
tff(f38,axiom,(
  ! [X2 : 'Nat_0()',X1 : 'Nat_0()',X0 : 'Bool_0()'] : (x_1(X0,X2,X1) => x_1(X0,'S_0'(X2),'S_0'(X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0'.smt2',unknown)).
tff(f125,plain,(
  ( ! [X0 : 'Nat_0()'] : (x_1(true_0,'S_0'('Z_0'),'S_0'('S_0'(X0)))) )),
  inference(unit_resulting_resolution,[],[f94,f102])).
tff(f94,plain,(
  ( ! [X0 : 'Nat_0()'] : (x_1(true_0,'Z_0','S_0'(X0))) )),
  inference(cnf_transformation,[],[f36])).
tff(f36,axiom,(
  ! [X0 : 'Nat_0()'] : x_1(true_0,'Z_0','S_0'(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0'.smt2',unknown)).
tff(f122,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (length_0('S_0'('S_0'('S_0'('Z_0'))),cons_0(X0,cons_0(X1,cons_0(X2,nil_0))))) )),
  inference(unit_resulting_resolution,[],[f121,f101])).
tff(f121,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (length_0('S_0'('S_0'('Z_0')),cons_0(X0,cons_0(X1,nil_0)))) )),
  inference(unit_resulting_resolution,[],[f120,f101])).
tff(f120,plain,(
  ( ! [X0 : 'Nat_0()'] : (length_0('S_0'('Z_0'),cons_0(X0,nil_0))) )),
  inference(unit_resulting_resolution,[],[f72,f101])).
tff(f72,plain,(
  length_0('Z_0',nil_0)),
  inference(cnf_transformation,[],[f34])).
tff(f34,axiom,(
  length_0('Z_0',nil_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0'.smt2',unknown)).
tff(f227,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'Nat_0()',X1 : 'Nat_0()'] : (sP2('Z_0',cons_0(X0,cons_0(X1,cons_0(X2,cons_0(X3,nil_0)))))) )),
  inference(unit_resulting_resolution,[],[f122,f172])).
tff(f172,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'list_0()'] : (sP2('Z_0',cons_0(X0,X1)) | ~length_0(X2,X1)) )),
  inference(resolution,[],[f166,f101])).
tff(f166,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'list_0()'] : (~length_0('S_0'(X0),X1) | sP2('Z_0',X1)) )),
  inference(resolution,[],[f112,f94])).
tff(f5850,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (sP0(cons_0(X0,cons_0('S_0'(X1),cons_0('Z_0',cons_0(X2,nil_0)))))) )),
  inference(unit_resulting_resolution,[],[f199,f140,f3440])).
tff(f3440,plain,(
  ( ! [X26 : 'Nat_0()',X24 : 'list_0()',X23 : 'list_0()',X25 : 'Nat_0()'] : (~diseqlist_0(cons_0(X26,X23),cons_0(X25,cons_0(X26,X24))) | ~x_4(X23,X24,cons_0(X25,nil_0)) | sP0(cons_0(X25,cons_0(X26,X24)))) )),
  inference(resolution,[],[f3130,f108])).
tff(f3130,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (rotate_0(cons_0(X0,X1),'S_0'('Z_0'),cons_0(X2,cons_0(X0,X3))) | ~x_4(X1,X3,cons_0(X2,nil_0))) )),
  inference(resolution,[],[f286,f91])).
tff(f286,plain,(
  ( ! [X6 : 'Nat_0()',X4 : 'Nat_0()',X8 : 'list_0()',X7 : 'list_0()',X5 : 'Nat_0()',X3 : 'list_0()'] : (~rotate_0(X3,X4,cons_0(X6,X8)) | rotate_0(X3,'S_0'(X4),cons_0(X5,cons_0(X6,X7))) | ~x_4(X8,X7,cons_0(X5,nil_0))) )),
  inference(resolution,[],[f106,f105])).
tff(f140,plain,(
  ( ! [X4 : 'list_0()',X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'Nat_0()',X1 : 'list_0()'] : (diseqlist_0(cons_0(X0,cons_0('Z_0',X1)),cons_0(X2,cons_0('S_0'(X3),X4)))) )),
  inference(unit_resulting_resolution,[],[f132,f104])).
tff(f104,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (diseqlist_0(cons_0(X0,X3),cons_0(X2,X1)) | ~diseqlist_0(X3,X1)) )),
  inference(cnf_transformation,[],[f59])).
tff(f59,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : (diseqlist_0(cons_0(X0,X3),cons_0(X2,X1)) | ~diseqlist_0(X3,X1))),
  inference(ennf_transformation,[],[f50])).
tff(f50,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : (diseqlist_0(X3,X1) => diseqlist_0(cons_0(X0,X3),cons_0(X2,X1)))),
  inference(rectify,[],[f32])).
tff(f32,axiom,(
  ! [X0 : 'Nat_0()',X3 : 'list_0()',X2 : 'Nat_0()',X1 : 'list_0()'] : (diseqlist_0(X1,X3) => diseqlist_0(cons_0(X0,X1),cons_0(X2,X3)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0'.smt2',unknown)).
tff(f132,plain,(
  ( ! [X2 : 'list_0()',X0 : 'list_0()',X1 : 'Nat_0()'] : (diseqlist_0(cons_0('Z_0',X0),cons_0('S_0'(X1),X2))) )),
  inference(unit_resulting_resolution,[],[f87,f103])).
tff(f103,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (diseqlist_0(cons_0(X0,X3),cons_0(X2,X1)) | ~diseqNat_0(X0,X2)) )),
  inference(cnf_transformation,[],[f58])).
tff(f58,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : (diseqlist_0(cons_0(X0,X3),cons_0(X2,X1)) | ~diseqNat_0(X0,X2))),
  inference(ennf_transformation,[],[f49])).
tff(f49,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : (diseqNat_0(X0,X2) => diseqlist_0(cons_0(X0,X3),cons_0(X2,X1)))),
  inference(rectify,[],[f31])).
tff(f31,axiom,(
  ! [X0 : 'Nat_0()',X3 : 'list_0()',X2 : 'Nat_0()',X1 : 'list_0()'] : (diseqNat_0(X0,X2) => diseqlist_0(cons_0(X0,X1),cons_0(X2,X3)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0'.smt2',unknown)).
tff(f87,plain,(
  ( ! [X0 : 'Nat_0()'] : (diseqNat_0('Z_0','S_0'(X0))) )),
  inference(cnf_transformation,[],[f23])).
tff(f23,axiom,(
  ! [X0 : 'Nat_0()'] : diseqNat_0('Z_0','S_0'(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0'.smt2',unknown)).
