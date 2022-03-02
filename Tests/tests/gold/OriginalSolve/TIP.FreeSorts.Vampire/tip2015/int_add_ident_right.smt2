3
12052
50
UNSAT
tff(type_def_5, type, 'Nat_0()': $tType).
tff(type_def_6, type, 'Integer_0()': $tType).
tff(func_def_0, type, zero_0: 'Nat_0()').
tff(func_def_1, type, succ_0: ('Nat_0()') > 'Nat_0()').
tff(func_def_2, type, 'P_1': ('Nat_0()') > 'Integer_0()').
tff(func_def_3, type, 'N_0': ('Nat_0()') > 'Integer_0()').
tff(pred_def_1, type, diseqNat_0: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_2, type, p_2: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_3, type, iszero_0: ('Nat_0()') > $o).
tff(pred_def_4, type, issucc_0: ('Nat_0()') > $o).
tff(pred_def_5, type, diseqInteger_0: ('Integer_0()' * 'Integer_0()') > $o).
tff(pred_def_6, type, projP_1: ('Nat_0()' * 'Integer_0()') > $o).
tff(pred_def_7, type, projN_1: ('Nat_0()' * 'Integer_0()') > $o).
tff(pred_def_8, type, isP_0: ('Integer_0()') > $o).
tff(pred_def_9, type, isN_0: ('Integer_0()') > $o).
tff(pred_def_10, type, zero_1: ('Integer_0()') > $o).
tff(pred_def_11, type, plus_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_12, type, x_1: ('Integer_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_13, type, plus_1: ('Integer_0()' * 'Integer_0()' * 'Integer_0()') > $o).
tff(pred_def_14, type, sP0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_15, type, sP1: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(f1374,plain,(
  $false),
  inference(unit_resulting_resolution,[],[f75,f143,f134,f90])).
tff(f90,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'Integer_0()',X1 : 'Nat_0()'] : (plus_1(X3,'N_0'(X1),'P_1'(X0)) | ~plus_0(X2,succ_0(zero_0),X1) | ~x_1(X3,X0,X2)) )),
  inference(cnf_transformation,[],[f59])).
tff(f59,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'Integer_0()'] : (plus_1(X3,'N_0'(X1),'P_1'(X0)) | ~plus_0(X2,succ_0(zero_0),X1) | ~x_1(X3,X0,X2))),
  inference(flattening,[],[f58])).
tff(f58,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'Integer_0()'] : (plus_1(X3,'N_0'(X1),'P_1'(X0)) | (~plus_0(X2,succ_0(zero_0),X1) | ~x_1(X3,X0,X2)))),
  inference(ennf_transformation,[],[f42])).
tff(f42,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'Integer_0()'] : ((plus_0(X2,succ_0(zero_0),X1) & x_1(X3,X0,X2)) => plus_1(X3,'N_0'(X1),'P_1'(X0)))),
  inference(rectify,[],[f23])).
tff(f23,axiom,(
  ! [X2 : 'Nat_0()',X3 : 'Nat_0()',X1 : 'Nat_0()',X0 : 'Integer_0()'] : ((plus_0(X1,succ_0(zero_0),X3) & x_1(X0,X2,X1)) => plus_1(X0,'N_0'(X3),'P_1'(X2)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_ident_right.smt2',unknown)).
tff(f134,plain,(
  ( ! [X0 : 'Nat_0()'] : (~plus_1('N_0'(succ_0(X0)),'N_0'(zero_0),'P_1'(zero_0))) )),
  inference(unit_resulting_resolution,[],[f115,f64,f87])).
tff(f87,plain,(
  ( ! [X2 : 'Integer_0()',X0 : 'Integer_0()',X1 : 'Integer_0()'] : (~plus_1(X1,X2,X0) | ~zero_1(X0) | ~diseqInteger_0(X2,X1)) )),
  inference(cnf_transformation,[],[f54])).
tff(f54,plain,(
  ! [X0 : 'Integer_0()',X1 : 'Integer_0()',X2 : 'Integer_0()'] : (~diseqInteger_0(X2,X1) | ~zero_1(X0) | ~plus_1(X1,X2,X0))),
  inference(ennf_transformation,[],[f39])).
tff(f39,plain,(
  ! [X0 : 'Integer_0()',X1 : 'Integer_0()',X2 : 'Integer_0()'] : ~(diseqInteger_0(X2,X1) & zero_1(X0) & plus_1(X1,X2,X0))),
  inference(true_and_false_elimination,[],[f26])).
tff(f26,axiom,(
  ! [X0 : 'Integer_0()',X1 : 'Integer_0()',X2 : 'Integer_0()'] : ((diseqInteger_0(X2,X1) & zero_1(X0) & plus_1(X1,X2,X0)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_ident_right.smt2',unknown)).
tff(f64,plain,(
  zero_1('P_1'(zero_0))),
  inference(cnf_transformation,[],[f15])).
tff(f15,axiom,(
  zero_1('P_1'(zero_0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_ident_right.smt2',unknown)).
tff(f115,plain,(
  ( ! [X0 : 'Nat_0()'] : (diseqInteger_0('N_0'(zero_0),'N_0'(succ_0(X0)))) )),
  inference(unit_resulting_resolution,[],[f69,f80])).
tff(f80,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (diseqInteger_0('N_0'(X0),'N_0'(X1)) | ~diseqNat_0(X0,X1)) )),
  inference(cnf_transformation,[],[f47])).
tff(f47,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (diseqInteger_0('N_0'(X0),'N_0'(X1)) | ~diseqNat_0(X0,X1))),
  inference(ennf_transformation,[],[f14])).
tff(f14,axiom,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (diseqNat_0(X0,X1) => diseqInteger_0('N_0'(X0),'N_0'(X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_ident_right.smt2',unknown)).
tff(f69,plain,(
  ( ! [X0 : 'Nat_0()'] : (diseqNat_0(zero_0,succ_0(X0))) )),
  inference(cnf_transformation,[],[f4])).
tff(f4,axiom,(
  ! [X0 : 'Nat_0()'] : diseqNat_0(zero_0,succ_0(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_ident_right.smt2',unknown)).
tff(f143,plain,(
  ( ! [X0 : 'Nat_0()'] : (plus_0(succ_0(X0),succ_0(zero_0),X0)) )),
  inference(unit_resulting_resolution,[],[f74,f84])).
tff(f84,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (plus_0(succ_0(X2),succ_0(X1),X0) | ~plus_0(X2,X1,X0)) )),
  inference(cnf_transformation,[],[f51])).
tff(f51,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (plus_0(succ_0(X2),succ_0(X1),X0) | ~plus_0(X2,X1,X0))),
  inference(ennf_transformation,[],[f36])).
tff(f36,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (plus_0(X2,X1,X0) => plus_0(succ_0(X2),succ_0(X1),X0))),
  inference(rectify,[],[f16])).
tff(f16,axiom,(
  ! [X2 : 'Nat_0()',X1 : 'Nat_0()',X0 : 'Nat_0()'] : (plus_0(X0,X1,X2) => plus_0(succ_0(X0),succ_0(X1),X2))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_ident_right.smt2',unknown)).
tff(f74,plain,(
  ( ! [X0 : 'Nat_0()'] : (plus_0(X0,zero_0,X0)) )),
  inference(cnf_transformation,[],[f17])).
tff(f17,axiom,(
  ! [X0 : 'Nat_0()'] : plus_0(X0,zero_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_ident_right.smt2',unknown)).
tff(f75,plain,(
  ( ! [X0 : 'Nat_0()'] : (x_1('N_0'(succ_0(X0)),zero_0,succ_0(X0))) )),
  inference(cnf_transformation,[],[f19])).
tff(f19,axiom,(
  ! [X0 : 'Nat_0()'] : x_1('N_0'(succ_0(X0)),zero_0,succ_0(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_ident_right.smt2',unknown)).
