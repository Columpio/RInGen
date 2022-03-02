1
11992
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
tff(f82,plain,(
  $false),
  inference(unit_resulting_resolution,[],[f33,f59,f44])).
tff(f44,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (diseqlist_0(cons_0(X0,X1),cons_0(X2,X3)) | ~diseqNat_0(X0,X2)) )),
  inference(cnf_transformation,[],[f27])).
tff(f27,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : (diseqlist_0(cons_0(X0,X1),cons_0(X2,X3)) | ~diseqNat_0(X0,X2))),
  inference(ennf_transformation,[],[f13])).
tff(f13,axiom,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : (diseqNat_0(X0,X2) => diseqlist_0(cons_0(X0,X1),cons_0(X2,X3)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_uhhhw2.smt2',unknown)).
tff(f59,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (~diseqlist_0(cons_0(X0,nil_0),cons_0(X1,nil_0))) )),
  inference(unit_resulting_resolution,[],[f52,f52,f43])).
tff(f43,plain,(
  ( ! [X2 : 'list_0()',X0 : 'Nat_0()',X1 : 'list_0()'] : (~length_0(X0,X2) | ~length_0(X0,X1) | ~diseqlist_0(X1,X2)) )),
  inference(cnf_transformation,[],[f26])).
tff(f26,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'list_0()'] : (~diseqlist_0(X1,X2) | ~length_0(X0,X1) | ~length_0(X0,X2))),
  inference(ennf_transformation,[],[f23])).
tff(f23,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'list_0()'] : ~(diseqlist_0(X1,X2) & length_0(X0,X1) & length_0(X0,X2))),
  inference(true_and_false_elimination,[],[f17])).
tff(f17,axiom,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'list_0()'] : ((diseqlist_0(X1,X2) & length_0(X0,X1) & length_0(X0,X2)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_uhhhw2.smt2',unknown)).
tff(f52,plain,(
  ( ! [X0 : 'Nat_0()'] : (length_0('S_0'('Z_0'),cons_0(X0,nil_0))) )),
  inference(unit_resulting_resolution,[],[f31,f42])).
tff(f42,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'list_0()',X1 : 'Nat_0()'] : (length_0('S_0'(X1),cons_0(X2,X0)) | ~length_0(X1,X0)) )),
  inference(cnf_transformation,[],[f25])).
tff(f25,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (length_0('S_0'(X1),cons_0(X2,X0)) | ~length_0(X1,X0))),
  inference(ennf_transformation,[],[f22])).
tff(f22,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (length_0(X1,X0) => length_0('S_0'(X1),cons_0(X2,X0)))),
  inference(rectify,[],[f15])).
tff(f15,axiom,(
  ! [X2 : 'list_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (length_0(X0,X2) => length_0('S_0'(X0),cons_0(X1,X2)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_uhhhw2.smt2',unknown)).
tff(f31,plain,(
  length_0('Z_0',nil_0)),
  inference(cnf_transformation,[],[f16])).
tff(f16,axiom,(
  length_0('Z_0',nil_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_uhhhw2.smt2',unknown)).
tff(f33,plain,(
  ( ! [X0 : 'Nat_0()'] : (diseqNat_0('Z_0','S_0'(X0))) )),
  inference(cnf_transformation,[],[f5])).
tff(f5,axiom,(
  ! [X0 : 'Nat_0()'] : diseqNat_0('Z_0','S_0'(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_uhhhw2.smt2',unknown)).
