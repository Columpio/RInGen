2
12368
30
UNSAT
tff(type_def_5, type, 'Nat_0()': $tType).
tff(type_def_6, type, 'list_0()': $tType).
tff(func_def_0, type, 'S_0': ('Nat_0()') > 'Nat_0()').
tff(func_def_1, type, 'Z_0': 'Nat_0()').
tff(func_def_2, type, nil_0: 'list_0()').
tff(func_def_3, type, cons_0: ('Nat_0()' * 'list_0()') > 'list_0()').
tff(pred_def_1, type, diseqNat_0: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_2, type, projS_1: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_3, type, isS_0: ('Nat_0()') > $o).
tff(pred_def_4, type, isZ_2: ('Nat_0()') > $o).
tff(pred_def_5, type, diseqlist_0: ('list_0()' * 'list_0()') > $o).
tff(pred_def_6, type, head_1: ('Nat_0()' * 'list_0()') > $o).
tff(pred_def_7, type, tail_1: ('list_0()' * 'list_0()') > $o).
tff(pred_def_8, type, isnil_0: ('list_0()') > $o).
tff(pred_def_9, type, iscons_0: ('list_0()') > $o).
tff(pred_def_10, type, length_0: ('Nat_0()' * 'list_0()') > $o).
tff(pred_def_11, type, x_1: ('list_0()' * 'list_0()' * 'list_0()') > $o).
tff(pred_def_12, type, rotate_0: ('list_0()' * 'Nat_0()' * 'list_0()') > $o).
tff(pred_def_13, type, sP0: ('list_0()' * 'list_0()' * 'list_0()') > $o).
tff(f163,plain,(
  $false),
  inference(unit_resulting_resolution,[],[f54,f50,f50,f94,f66])).
tff(f66,plain,(
  ( ! [X2 : 'list_0()',X0 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~sP0(X3,X2,X0) | ~x_1(X2,X0,X1) | ~x_1(X3,X0,X1) | ~diseqlist_0(X0,X1)) )),
  inference(general_splitting,[],[f63,f65_D])).
tff(f65,plain,(
  ( ! [X4 : 'Nat_0()',X2 : 'list_0()',X0 : 'list_0()',X3 : 'list_0()'] : (~rotate_0(X3,X4,X2) | ~length_0(X4,X0) | sP0(X3,X2,X0)) )),
  inference(cnf_transformation,[],[f65_D])).
tff(f65_D,plain,(
  ( ! [X0,X2,X3] : (( ! [X4] : (~rotate_0(X3,X4,X2) | ~length_0(X4,X0)) ) <=> ~sP0(X3,X2,X0)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP0])])).
tff(f63,plain,(
  ( ! [X4 : 'Nat_0()',X2 : 'list_0()',X0 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~diseqlist_0(X0,X1) | ~length_0(X4,X0) | ~x_1(X2,X0,X1) | ~rotate_0(X3,X4,X2) | ~x_1(X3,X0,X1)) )),
  inference(cnf_transformation,[],[f40])).
tff(f40,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()',X4 : 'Nat_0()'] : (~diseqlist_0(X0,X1) | ~length_0(X4,X0) | ~x_1(X2,X0,X1) | ~rotate_0(X3,X4,X2) | ~x_1(X3,X0,X1))),
  inference(ennf_transformation,[],[f33])).
tff(f33,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()',X4 : 'Nat_0()'] : ~(diseqlist_0(X0,X1) & length_0(X4,X0) & x_1(X2,X0,X1) & rotate_0(X3,X4,X2) & x_1(X3,X0,X1))),
  inference(true_and_false_elimination,[],[f32])).
tff(f32,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()',X4 : 'Nat_0()'] : ((diseqlist_0(X0,X1) & length_0(X4,X0) & x_1(X2,X0,X1) & rotate_0(X3,X4,X2) & x_1(X3,X0,X1)) => $false)),
  inference(rectify,[],[f22])).
tff(f22,axiom,(
  ! [X3 : 'list_0()',X4 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X0 : 'Nat_0()'] : ((diseqlist_0(X3,X4) & length_0(X0,X3) & x_1(X1,X3,X4) & rotate_0(X2,X0,X1) & x_1(X2,X3,X4)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_uhhhw1.smt2',unknown)).
tff(f94,plain,(
  ( ! [X0 : 'list_0()'] : (sP0(X0,X0,nil_0)) )),
  inference(unit_resulting_resolution,[],[f45,f51,f65])).
tff(f51,plain,(
  ( ! [X0 : 'list_0()'] : (rotate_0(X0,'Z_0',X0)) )),
  inference(cnf_transformation,[],[f19])).
tff(f19,axiom,(
  ! [X0 : 'list_0()'] : rotate_0(X0,'Z_0',X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_uhhhw1.smt2',unknown)).
tff(f45,plain,(
  length_0('Z_0',nil_0)),
  inference(cnf_transformation,[],[f16])).
tff(f16,axiom,(
  length_0('Z_0',nil_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_uhhhw1.smt2',unknown)).
tff(f50,plain,(
  ( ! [X0 : 'list_0()'] : (x_1(X0,nil_0,X0)) )),
  inference(cnf_transformation,[],[f18])).
tff(f18,axiom,(
  ! [X0 : 'list_0()'] : x_1(X0,nil_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_uhhhw1.smt2',unknown)).
tff(f54,plain,(
  ( ! [X0 : 'list_0()',X1 : 'Nat_0()'] : (diseqlist_0(nil_0,cons_0(X1,X0))) )),
  inference(cnf_transformation,[],[f23])).
tff(f23,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()'] : diseqlist_0(nil_0,cons_0(X1,X0))),
  inference(rectify,[],[f11])).
tff(f11,axiom,(
  ! [X1 : 'list_0()',X0 : 'Nat_0()'] : diseqlist_0(nil_0,cons_0(X0,X1))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_uhhhw1.smt2',unknown)).
