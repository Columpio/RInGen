2
12048
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
tff(pred_def_10, type, drop_0: ('list_0()' * 'Nat_0()' * 'list_0()') > $o).
tff(f102,plain,(
  $false),
  inference(unit_resulting_resolution,[],[f37,f40,f39,f50])).
tff(f50,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'list_0()',X3 : 'list_0()',X1 : 'Nat_0()'] : (~drop_0(X3,X2,X0) | ~drop_0(X3,X1,X0) | ~diseqNat_0(X1,X2)) )),
  inference(cnf_transformation,[],[f32])).
tff(f32,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : (~diseqNat_0(X1,X2) | ~drop_0(X3,X1,X0) | ~drop_0(X3,X2,X0))),
  inference(ennf_transformation,[],[f27])).
tff(f27,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : ~(diseqNat_0(X1,X2) & drop_0(X3,X1,X0) & drop_0(X3,X2,X0))),
  inference(true_and_false_elimination,[],[f26])).
tff(f26,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : ((diseqNat_0(X1,X2) & drop_0(X3,X1,X0) & drop_0(X3,X2,X0)) => $false)),
  inference(rectify,[],[f18])).
tff(f18,axiom,(
  ! [X3 : 'list_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X0 : 'list_0()'] : ((diseqNat_0(X1,X2) & drop_0(X0,X1,X3) & drop_0(X0,X2,X3)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_drop_inj1.smt2',unknown)).
tff(f39,plain,(
  ( ! [X0 : 'list_0()'] : (drop_0(X0,'Z_0',X0)) )),
  inference(cnf_transformation,[],[f15])).
tff(f15,axiom,(
  ! [X0 : 'list_0()'] : drop_0(X0,'Z_0',X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_drop_inj1.smt2',unknown)).
tff(f40,plain,(
  ( ! [X0 : 'Nat_0()'] : (drop_0(nil_0,'S_0'(X0),nil_0)) )),
  inference(cnf_transformation,[],[f17])).
tff(f17,axiom,(
  ! [X0 : 'Nat_0()'] : drop_0(nil_0,'S_0'(X0),nil_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_drop_inj1.smt2',unknown)).
tff(f37,plain,(
  ( ! [X0 : 'Nat_0()'] : (diseqNat_0('S_0'(X0),'Z_0')) )),
  inference(cnf_transformation,[],[f4])).
tff(f4,axiom,(
  ! [X0 : 'Nat_0()'] : diseqNat_0('S_0'(X0),'Z_0')),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_drop_inj1.smt2',unknown)).
