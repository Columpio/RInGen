3
13200
70
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
tff(pred_def_10, type, plus_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_11, type, x_1: ('Integer_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_12, type, plus_1: ('Integer_0()' * 'Integer_0()' * 'Integer_0()') > $o).
tff(pred_def_13, type, sP0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_14, type, sP1: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_15, type, sP2: ('Integer_0()' * 'Integer_0()' * 'Integer_0()') > $o).
tff(pred_def_16, type, sP3: ('Integer_0()' * 'Integer_0()' * 'Integer_0()' * 'Integer_0()') > $o).
tff(f2482,plain,(
  $false),
  inference(subsumption_resolution,[],[f2468,f2454])).
tff(f2454,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (sP3('P_1'(X0),'P_1'(succ_0(zero_0)),'N_0'(succ_0(X1)),'P_1'(succ_0(zero_0)))) )),
  inference(unit_resulting_resolution,[],[f2339,f2448,f100])).
tff(f100,plain,(
  ( ! [X6 : 'Integer_0()',X2 : 'Integer_0()',X0 : 'Integer_0()',X3 : 'Integer_0()',X1 : 'Integer_0()'] : (sP3(X3,X2,X1,X0) | ~sP2(X3,X0,X6) | ~plus_1(X6,X1,X2)) )),
  inference(cnf_transformation,[],[f100_D])).
tff(f100_D,plain,(
  ( ! [X0,X1,X2,X3] : (( ! [X6] : (~sP2(X3,X0,X6) | ~plus_1(X6,X1,X2)) ) <=> ~sP3(X3,X2,X1,X0)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
tff(f2448,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (sP2('P_1'(X0),'P_1'(succ_0(zero_0)),'N_0'(succ_0(X1)))) )),
  inference(unit_resulting_resolution,[],[f79,f2339,f98])).
tff(f98,plain,(
  ( ! [X6 : 'Integer_0()',X0 : 'Integer_0()',X5 : 'Integer_0()',X3 : 'Integer_0()'] : (~plus_1(X5,X6,X0) | ~diseqInteger_0(X3,X5) | sP2(X3,X0,X6)) )),
  inference(cnf_transformation,[],[f98_D])).
tff(f98_D,plain,(
  ( ! [X6,X0,X3] : (( ! [X5] : (~plus_1(X5,X6,X0) | ~diseqInteger_0(X3,X5)) ) <=> ~sP2(X3,X0,X6)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).
tff(f79,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (diseqInteger_0('P_1'(X0),'N_0'(X1))) )),
  inference(cnf_transformation,[],[f11])).
tff(f11,axiom,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : diseqInteger_0('P_1'(X0),'N_0'(X1))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_assoc.smt2',unknown)).
tff(f2339,plain,(
  ( ! [X0 : 'Nat_0()'] : (plus_1('N_0'(succ_0(X0)),'N_0'(succ_0(X0)),'P_1'(succ_0(zero_0)))) )),
  inference(unit_resulting_resolution,[],[f167,f138,f90])).
tff(f90,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Integer_0()',X3 : 'Nat_0()',X1 : 'Nat_0()'] : (plus_1(X0,'N_0'(X2),'P_1'(X1)) | ~plus_0(X3,succ_0(zero_0),X2) | ~x_1(X0,X1,X3)) )),
  inference(cnf_transformation,[],[f60])).
tff(f60,plain,(
  ! [X0 : 'Integer_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'Nat_0()'] : (plus_1(X0,'N_0'(X2),'P_1'(X1)) | ~plus_0(X3,succ_0(zero_0),X2) | ~x_1(X0,X1,X3))),
  inference(flattening,[],[f59])).
tff(f59,plain,(
  ! [X0 : 'Integer_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'Nat_0()'] : (plus_1(X0,'N_0'(X2),'P_1'(X1)) | (~plus_0(X3,succ_0(zero_0),X2) | ~x_1(X0,X1,X3)))),
  inference(ennf_transformation,[],[f42])).
tff(f42,plain,(
  ! [X0 : 'Integer_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'Nat_0()'] : ((plus_0(X3,succ_0(zero_0),X2) & x_1(X0,X1,X3)) => plus_1(X0,'N_0'(X2),'P_1'(X1)))),
  inference(rectify,[],[f22])).
tff(f22,axiom,(
  ! [X0 : 'Integer_0()',X2 : 'Nat_0()',X3 : 'Nat_0()',X1 : 'Nat_0()'] : ((plus_0(X1,succ_0(zero_0),X3) & x_1(X0,X2,X1)) => plus_1(X0,'N_0'(X3),'P_1'(X2)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_assoc.smt2',unknown)).
tff(f138,plain,(
  ( ! [X0 : 'Nat_0()'] : (plus_0(succ_0(X0),succ_0(zero_0),X0)) )),
  inference(unit_resulting_resolution,[],[f75,f85])).
tff(f85,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (plus_0(succ_0(X2),succ_0(X1),X0) | ~plus_0(X2,X1,X0)) )),
  inference(cnf_transformation,[],[f53])).
tff(f53,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (plus_0(succ_0(X2),succ_0(X1),X0) | ~plus_0(X2,X1,X0))),
  inference(ennf_transformation,[],[f36])).
tff(f36,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (plus_0(X2,X1,X0) => plus_0(succ_0(X2),succ_0(X1),X0))),
  inference(rectify,[],[f15])).
tff(f15,axiom,(
  ! [X2 : 'Nat_0()',X1 : 'Nat_0()',X0 : 'Nat_0()'] : (plus_0(X0,X1,X2) => plus_0(succ_0(X0),succ_0(X1),X2))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_assoc.smt2',unknown)).
tff(f75,plain,(
  ( ! [X0 : 'Nat_0()'] : (plus_0(X0,zero_0,X0)) )),
  inference(cnf_transformation,[],[f16])).
tff(f16,axiom,(
  ! [X0 : 'Nat_0()'] : plus_0(X0,zero_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_assoc.smt2',unknown)).
tff(f167,plain,(
  ( ! [X0 : 'Nat_0()'] : (x_1('N_0'(succ_0(X0)),succ_0(zero_0),succ_0(succ_0(X0)))) )),
  inference(unit_resulting_resolution,[],[f76,f87])).
tff(f87,plain,(
  ( ! [X2 : 'Integer_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (x_1(X2,succ_0(X1),succ_0(X0)) | ~x_1(X2,X1,X0)) )),
  inference(cnf_transformation,[],[f55])).
tff(f55,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Integer_0()'] : (x_1(X2,succ_0(X1),succ_0(X0)) | ~x_1(X2,X1,X0))),
  inference(ennf_transformation,[],[f38])).
tff(f38,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Integer_0()'] : (x_1(X2,X1,X0) => x_1(X2,succ_0(X1),succ_0(X0)))),
  inference(rectify,[],[f17])).
tff(f17,axiom,(
  ! [X1 : 'Nat_0()',X0 : 'Nat_0()',X2 : 'Integer_0()'] : (x_1(X2,X0,X1) => x_1(X2,succ_0(X0),succ_0(X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_assoc.smt2',unknown)).
tff(f76,plain,(
  ( ! [X0 : 'Nat_0()'] : (x_1('N_0'(succ_0(X0)),zero_0,succ_0(X0))) )),
  inference(cnf_transformation,[],[f18])).
tff(f18,axiom,(
  ! [X0 : 'Nat_0()'] : x_1('N_0'(succ_0(X0)),zero_0,succ_0(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_assoc.smt2',unknown)).
tff(f2468,plain,(
  ~sP3('P_1'(zero_0),'P_1'(succ_0(zero_0)),'N_0'(succ_0(zero_0)),'P_1'(succ_0(zero_0)))),
  inference(unit_resulting_resolution,[],[f192,f2334,f101])).
tff(f101,plain,(
  ( ! [X4 : 'Integer_0()',X2 : 'Integer_0()',X0 : 'Integer_0()',X3 : 'Integer_0()',X1 : 'Integer_0()'] : (~sP3(X3,X2,X1,X0) | ~plus_1(X3,X1,X4) | ~plus_1(X4,X2,X0)) )),
  inference(general_splitting,[],[f99,f100_D])).
tff(f99,plain,(
  ( ! [X6 : 'Integer_0()',X4 : 'Integer_0()',X2 : 'Integer_0()',X0 : 'Integer_0()',X3 : 'Integer_0()',X1 : 'Integer_0()'] : (~plus_1(X4,X2,X0) | ~plus_1(X3,X1,X4) | ~plus_1(X6,X1,X2) | ~sP2(X3,X0,X6)) )),
  inference(general_splitting,[],[f93,f98_D])).
tff(f93,plain,(
  ( ! [X6 : 'Integer_0()',X4 : 'Integer_0()',X2 : 'Integer_0()',X0 : 'Integer_0()',X5 : 'Integer_0()',X3 : 'Integer_0()',X1 : 'Integer_0()'] : (~diseqInteger_0(X3,X5) | ~plus_1(X4,X2,X0) | ~plus_1(X3,X1,X4) | ~plus_1(X6,X1,X2) | ~plus_1(X5,X6,X0)) )),
  inference(cnf_transformation,[],[f64])).
tff(f64,plain,(
  ! [X0 : 'Integer_0()',X1 : 'Integer_0()',X2 : 'Integer_0()',X3 : 'Integer_0()',X4 : 'Integer_0()',X5 : 'Integer_0()',X6 : 'Integer_0()'] : (~diseqInteger_0(X3,X5) | ~plus_1(X4,X2,X0) | ~plus_1(X3,X1,X4) | ~plus_1(X6,X1,X2) | ~plus_1(X5,X6,X0))),
  inference(ennf_transformation,[],[f47])).
tff(f47,plain,(
  ! [X0 : 'Integer_0()',X1 : 'Integer_0()',X2 : 'Integer_0()',X3 : 'Integer_0()',X4 : 'Integer_0()',X5 : 'Integer_0()',X6 : 'Integer_0()'] : ~(diseqInteger_0(X3,X5) & plus_1(X4,X2,X0) & plus_1(X3,X1,X4) & plus_1(X6,X1,X2) & plus_1(X5,X6,X0))),
  inference(true_and_false_elimination,[],[f46])).
tff(f46,plain,(
  ! [X0 : 'Integer_0()',X1 : 'Integer_0()',X2 : 'Integer_0()',X3 : 'Integer_0()',X4 : 'Integer_0()',X5 : 'Integer_0()',X6 : 'Integer_0()'] : ((diseqInteger_0(X3,X5) & plus_1(X4,X2,X0) & plus_1(X3,X1,X4) & plus_1(X6,X1,X2) & plus_1(X5,X6,X0)) => $false)),
  inference(rectify,[],[f25])).
tff(f25,axiom,(
  ! [X6 : 'Integer_0()',X4 : 'Integer_0()',X5 : 'Integer_0()',X1 : 'Integer_0()',X0 : 'Integer_0()',X3 : 'Integer_0()',X2 : 'Integer_0()'] : ((diseqInteger_0(X1,X3) & plus_1(X0,X5,X6) & plus_1(X1,X4,X0) & plus_1(X2,X4,X5) & plus_1(X3,X2,X6)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_assoc.smt2',unknown)).
tff(f2334,plain,(
  plus_1('P_1'(zero_0),'N_0'(succ_0(zero_0)),'P_1'(succ_0(succ_0(zero_0))))),
  inference(unit_resulting_resolution,[],[f169,f138,f90])).
tff(f169,plain,(
  x_1('P_1'(zero_0),succ_0(succ_0(zero_0)),succ_0(succ_0(zero_0)))),
  inference(unit_resulting_resolution,[],[f166,f87])).
tff(f166,plain,(
  x_1('P_1'(zero_0),succ_0(zero_0),succ_0(zero_0))),
  inference(unit_resulting_resolution,[],[f66,f87])).
tff(f66,plain,(
  x_1('P_1'(zero_0),zero_0,zero_0)),
  inference(cnf_transformation,[],[f20])).
tff(f20,axiom,(
  x_1('P_1'(zero_0),zero_0,zero_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_assoc.smt2',unknown)).
tff(f192,plain,(
  ( ! [X0 : 'Nat_0()'] : (plus_1('P_1'(succ_0(X0)),'P_1'(succ_0(zero_0)),'P_1'(X0))) )),
  inference(unit_resulting_resolution,[],[f138,f86])).
tff(f86,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (plus_1('P_1'(X0),'P_1'(X1),'P_1'(X2)) | ~plus_0(X0,X1,X2)) )),
  inference(cnf_transformation,[],[f54])).
tff(f54,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (plus_1('P_1'(X0),'P_1'(X1),'P_1'(X2)) | ~plus_0(X0,X1,X2))),
  inference(ennf_transformation,[],[f37])).
tff(f37,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (plus_0(X0,X1,X2) => plus_1('P_1'(X0),'P_1'(X1),'P_1'(X2)))),
  inference(rectify,[],[f24])).
tff(f24,axiom,(
  ! [X0 : 'Nat_0()',X2 : 'Nat_0()',X1 : 'Nat_0()'] : (plus_0(X0,X2,X1) => plus_1('P_1'(X0),'P_1'(X2),'P_1'(X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_add_assoc.smt2',unknown)).
