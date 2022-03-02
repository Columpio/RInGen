2
12352
50
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
tff(pred_def_11, type, sP0: ('list_0()' * 'list_0()' * 'Nat_0()') > $o).
tff(f162,plain,(
  $false),
  inference(unit_resulting_resolution,[],[f73,f73,f86,f48])).
tff(f48,plain,(
  ( ! [X2 : 'list_0()',X0 : 'list_0()',X3 : 'list_0()',X1 : 'Nat_0()'] : (~sP0(X3,X2,X1) | ~drop_0(X3,X1,X0) | ~drop_0(X2,X1,X0)) )),
  inference(general_splitting,[],[f46,f47_D])).
tff(f47,plain,(
  ( ! [X4 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()',X1 : 'Nat_0()'] : (~drop_0(X4,X1,X2) | ~diseqlist_0(X4,X3) | sP0(X3,X2,X1)) )),
  inference(cnf_transformation,[],[f47_D])).
tff(f47_D,plain,(
  ( ! [X1,X2,X3] : (( ! [X4] : (~drop_0(X4,X1,X2) | ~diseqlist_0(X4,X3)) ) <=> ~sP0(X3,X2,X1)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP0])])).
tff(f46,plain,(
  ( ! [X4 : 'list_0()',X2 : 'list_0()',X0 : 'list_0()',X3 : 'list_0()',X1 : 'Nat_0()'] : (~diseqlist_0(X4,X3) | ~drop_0(X2,X1,X0) | ~drop_0(X4,X1,X2) | ~drop_0(X3,X1,X0)) )),
  inference(cnf_transformation,[],[f28])).
tff(f28,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'list_0()',X3 : 'list_0()',X4 : 'list_0()'] : (~diseqlist_0(X4,X3) | ~drop_0(X2,X1,X0) | ~drop_0(X4,X1,X2) | ~drop_0(X3,X1,X0))),
  inference(ennf_transformation,[],[f23])).
tff(f23,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'list_0()',X3 : 'list_0()',X4 : 'list_0()'] : ~(diseqlist_0(X4,X3) & drop_0(X2,X1,X0) & drop_0(X4,X1,X2) & drop_0(X3,X1,X0))),
  inference(true_and_false_elimination,[],[f22])).
tff(f22,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'list_0()',X3 : 'list_0()',X4 : 'list_0()'] : ((diseqlist_0(X4,X3) & drop_0(X2,X1,X0) & drop_0(X4,X1,X2) & drop_0(X3,X1,X0)) => $false)),
  inference(rectify,[],[f18])).
tff(f18,axiom,(
  ! [X4 : 'list_0()',X3 : 'Nat_0()',X0 : 'list_0()',X2 : 'list_0()',X1 : 'list_0()'] : ((diseqlist_0(X1,X2) & drop_0(X0,X3,X4) & drop_0(X1,X3,X0) & drop_0(X2,X3,X4)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_drop_idem.smt2',unknown)).
tff(f86,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'list_0()'] : (sP0(cons_0(X0,X1),cons_0(X2,nil_0),'S_0'('Z_0'))) )),
  inference(unit_resulting_resolution,[],[f38,f73,f47])).
tff(f38,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'list_0()'] : (diseqlist_0(nil_0,cons_0(X0,X1))) )),
  inference(cnf_transformation,[],[f11])).
tff(f11,axiom,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()'] : diseqlist_0(nil_0,cons_0(X0,X1))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_drop_idem.smt2',unknown)).
tff(f73,plain,(
  ( ! [X0 : 'list_0()',X1 : 'Nat_0()'] : (drop_0(X0,'S_0'('Z_0'),cons_0(X1,X0))) )),
  inference(unit_resulting_resolution,[],[f35,f45])).
tff(f45,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'list_0()',X3 : 'list_0()',X1 : 'Nat_0()'] : (drop_0(X0,'S_0'(X2),cons_0(X1,X3)) | ~drop_0(X0,X2,X3)) )),
  inference(cnf_transformation,[],[f27])).
tff(f27,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : (drop_0(X0,'S_0'(X2),cons_0(X1,X3)) | ~drop_0(X0,X2,X3))),
  inference(ennf_transformation,[],[f21])).
tff(f21,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : (drop_0(X0,X2,X3) => drop_0(X0,'S_0'(X2),cons_0(X1,X3)))),
  inference(rectify,[],[f16])).
tff(f16,axiom,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X3 : 'Nat_0()',X2 : 'list_0()'] : (drop_0(X0,X3,X2) => drop_0(X0,'S_0'(X3),cons_0(X1,X2)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_drop_idem.smt2',unknown)).
tff(f35,plain,(
  ( ! [X0 : 'list_0()'] : (drop_0(X0,'Z_0',X0)) )),
  inference(cnf_transformation,[],[f15])).
tff(f15,axiom,(
  ! [X0 : 'list_0()'] : drop_0(X0,'Z_0',X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_drop_idem.smt2',unknown)).
