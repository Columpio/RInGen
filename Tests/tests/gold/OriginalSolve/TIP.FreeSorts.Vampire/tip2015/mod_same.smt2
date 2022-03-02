3
12388
30
UNSAT
tff(type_def_5, type, 'Bool_0()': $tType).
tff(type_def_6, type, 'Nat_0()': $tType).
tff(func_def_0, type, false_0: 'Bool_0()').
tff(func_def_1, type, true_0: 'Bool_0()').
tff(func_def_2, type, zero_0: 'Nat_0()').
tff(func_def_3, type, succ_0: ('Nat_0()') > 'Nat_0()').
tff(pred_def_1, type, diseqBool_0: ('Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_2, type, isfalse_1: ('Bool_0()') > $o).
tff(pred_def_3, type, istrue_1: ('Bool_0()') > $o).
tff(pred_def_4, type, and_0: ('Bool_0()' * 'Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_5, type, or_0: ('Bool_0()' * 'Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_6, type, hence_0: ('Bool_0()' * 'Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_7, type, not_0: ('Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_8, type, diseqNat_0: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_9, type, p_1: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_10, type, iszero_0: ('Nat_0()') > $o).
tff(pred_def_11, type, issucc_0: ('Nat_0()') > $o).
tff(pred_def_12, type, minus_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_13, type, lt_0: ('Bool_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_14, type, mod_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_15, type, go_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_16, type, modstructural_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_17, type, sP0: ('Nat_0()' * 'Nat_0()') > $o).
tff(f218,plain,(
  $false),
  inference(unit_resulting_resolution,[],[f205,f153,f99])).
tff(f99,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (~go_0(X1,X2,X0,succ_0(X0)) | go_0(X1,succ_0(X2),zero_0,succ_0(X0))) )),
  inference(cnf_transformation,[],[f58])).
tff(f58,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (go_0(X1,succ_0(X2),zero_0,succ_0(X0)) | ~go_0(X1,X2,X0,succ_0(X0)))),
  inference(ennf_transformation,[],[f47])).
tff(f47,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (go_0(X1,X2,X0,succ_0(X0)) => go_0(X1,succ_0(X2),zero_0,succ_0(X0)))),
  inference(rectify,[],[f35])).
tff(f35,axiom,(
  ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (go_0(X0,X1,X2,succ_0(X2)) => go_0(X0,succ_0(X1),zero_0,succ_0(X2)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/mod_same.smt2',unknown)).
tff(f153,plain,(
  ( ! [X0 : 'Nat_0()'] : (~go_0(zero_0,succ_0(zero_0),zero_0,succ_0(succ_0(X0)))) )),
  inference(unit_resulting_resolution,[],[f140,f97])).
tff(f97,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (~go_0(X1,X0,zero_0,X2) | modstructural_0(X1,X0,X2)) )),
  inference(cnf_transformation,[],[f56])).
tff(f56,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (modstructural_0(X1,X0,X2) | ~go_0(X1,X0,zero_0,X2))),
  inference(ennf_transformation,[],[f45])).
tff(f45,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (go_0(X1,X0,zero_0,X2) => modstructural_0(X1,X0,X2))),
  inference(rectify,[],[f39])).
tff(f39,axiom,(
  ! [X1 : 'Nat_0()',X0 : 'Nat_0()',X2 : 'Nat_0()'] : (go_0(X0,X1,zero_0,X2) => modstructural_0(X0,X1,X2))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/mod_same.smt2',unknown)).
tff(f140,plain,(
  ( ! [X0 : 'Nat_0()'] : (~modstructural_0(zero_0,succ_0(zero_0),succ_0(succ_0(X0)))) )),
  inference(unit_resulting_resolution,[],[f84,f121,f101])).
tff(f101,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'Nat_0()',X1 : 'Nat_0()'] : (~modstructural_0(X3,X2,X1) | ~mod_0(X0,X2,X1) | ~diseqNat_0(X0,X3)) )),
  inference(cnf_transformation,[],[f60])).
tff(f60,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'Nat_0()'] : (~diseqNat_0(X0,X3) | ~mod_0(X0,X2,X1) | ~modstructural_0(X3,X2,X1))),
  inference(ennf_transformation,[],[f50])).
tff(f50,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'Nat_0()'] : ~(diseqNat_0(X0,X3) & mod_0(X0,X2,X1) & modstructural_0(X3,X2,X1))),
  inference(true_and_false_elimination,[],[f49])).
tff(f49,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'Nat_0()'] : ((diseqNat_0(X0,X3) & mod_0(X0,X2,X1) & modstructural_0(X3,X2,X1)) => $false)),
  inference(rectify,[],[f40])).
tff(f40,axiom,(
  ! [X0 : 'Nat_0()',X3 : 'Nat_0()',X2 : 'Nat_0()',X1 : 'Nat_0()'] : ((diseqNat_0(X0,X1) & mod_0(X0,X2,X3) & modstructural_0(X1,X2,X3)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/mod_same.smt2',unknown)).
tff(f121,plain,(
  ( ! [X0 : 'Nat_0()'] : (mod_0(succ_0(zero_0),succ_0(zero_0),succ_0(succ_0(X0)))) )),
  inference(unit_resulting_resolution,[],[f118,f94])).
tff(f94,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (~lt_0(true_0,X1,succ_0(X0)) | mod_0(X1,X1,succ_0(X0))) )),
  inference(cnf_transformation,[],[f53])).
tff(f53,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (mod_0(X1,X1,succ_0(X0)) | ~lt_0(true_0,X1,succ_0(X0)))),
  inference(ennf_transformation,[],[f42])).
tff(f42,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (lt_0(true_0,X1,succ_0(X0)) => mod_0(X1,X1,succ_0(X0)))),
  inference(rectify,[],[f31])).
tff(f31,axiom,(
  ! [X1 : 'Nat_0()',X0 : 'Nat_0()'] : (lt_0(true_0,X0,succ_0(X1)) => mod_0(X0,X0,succ_0(X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/mod_same.smt2',unknown)).
tff(f118,plain,(
  ( ! [X0 : 'Nat_0()'] : (lt_0(true_0,succ_0(zero_0),succ_0(succ_0(X0)))) )),
  inference(unit_resulting_resolution,[],[f90,f95])).
tff(f95,plain,(
  ( ! [X2 : 'Bool_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (lt_0(X2,succ_0(X1),succ_0(X0)) | ~lt_0(X2,X1,X0)) )),
  inference(cnf_transformation,[],[f54])).
tff(f54,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Bool_0()'] : (lt_0(X2,succ_0(X1),succ_0(X0)) | ~lt_0(X2,X1,X0))),
  inference(ennf_transformation,[],[f43])).
tff(f43,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Bool_0()'] : (lt_0(X2,X1,X0) => lt_0(X2,succ_0(X1),succ_0(X0)))),
  inference(rectify,[],[f28])).
tff(f28,axiom,(
  ! [X2 : 'Nat_0()',X1 : 'Nat_0()',X0 : 'Bool_0()'] : (lt_0(X0,X1,X2) => lt_0(X0,succ_0(X1),succ_0(X2)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/mod_same.smt2',unknown)).
tff(f90,plain,(
  ( ! [X0 : 'Nat_0()'] : (lt_0(true_0,zero_0,succ_0(X0))) )),
  inference(cnf_transformation,[],[f29])).
tff(f29,axiom,(
  ! [X0 : 'Nat_0()'] : lt_0(true_0,zero_0,succ_0(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/mod_same.smt2',unknown)).
tff(f84,plain,(
  ( ! [X0 : 'Nat_0()'] : (diseqNat_0(succ_0(X0),zero_0)) )),
  inference(cnf_transformation,[],[f23])).
tff(f23,axiom,(
  ! [X0 : 'Nat_0()'] : diseqNat_0(succ_0(X0),zero_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/mod_same.smt2',unknown)).
tff(f205,plain,(
  ( ! [X0 : 'Nat_0()'] : (go_0(zero_0,zero_0,succ_0(zero_0),succ_0(succ_0(X0)))) )),
  inference(unit_resulting_resolution,[],[f129,f98])).
tff(f98,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (go_0(X2,zero_0,succ_0(X1),succ_0(X0)) | ~minus_0(X2,succ_0(X0),succ_0(X1))) )),
  inference(cnf_transformation,[],[f57])).
tff(f57,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (go_0(X2,zero_0,succ_0(X1),succ_0(X0)) | ~minus_0(X2,succ_0(X0),succ_0(X1)))),
  inference(ennf_transformation,[],[f46])).
tff(f46,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (minus_0(X2,succ_0(X0),succ_0(X1)) => go_0(X2,zero_0,succ_0(X1),succ_0(X0)))),
  inference(rectify,[],[f36])).
tff(f36,axiom,(
  ! [X2 : 'Nat_0()',X1 : 'Nat_0()',X0 : 'Nat_0()'] : (minus_0(X0,succ_0(X2),succ_0(X1)) => go_0(X0,zero_0,succ_0(X1),succ_0(X2)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/mod_same.smt2',unknown)).
tff(f129,plain,(
  ( ! [X0 : 'Nat_0()'] : (minus_0(zero_0,succ_0(succ_0(X0)),succ_0(zero_0))) )),
  inference(unit_resulting_resolution,[],[f89,f96])).
tff(f96,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (minus_0(X2,succ_0(X0),succ_0(X1)) | ~minus_0(X2,X0,X1)) )),
  inference(cnf_transformation,[],[f55])).
tff(f55,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (minus_0(X2,succ_0(X0),succ_0(X1)) | ~minus_0(X2,X0,X1))),
  inference(ennf_transformation,[],[f44])).
tff(f44,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (minus_0(X2,X0,X1) => minus_0(X2,succ_0(X0),succ_0(X1)))),
  inference(rectify,[],[f25])).
tff(f25,axiom,(
  ! [X2 : 'Nat_0()',X1 : 'Nat_0()',X0 : 'Nat_0()'] : (minus_0(X0,X2,X1) => minus_0(X0,succ_0(X2),succ_0(X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/mod_same.smt2',unknown)).
tff(f89,plain,(
  ( ! [X0 : 'Nat_0()'] : (minus_0(zero_0,succ_0(X0),zero_0)) )),
  inference(cnf_transformation,[],[f26])).
tff(f26,axiom,(
  ! [X0 : 'Nat_0()'] : minus_0(zero_0,succ_0(X0),zero_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/mod_same.smt2',unknown)).
