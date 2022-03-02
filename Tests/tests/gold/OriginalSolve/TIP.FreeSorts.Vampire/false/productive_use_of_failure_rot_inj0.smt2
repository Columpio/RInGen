2
12004
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
tff(pred_def_10, type, x_0: ('list_0()' * 'list_0()' * 'list_0()') > $o).
tff(pred_def_11, type, rotate_0: ('list_0()' * 'Nat_0()' * 'list_0()') > $o).
tff(pred_def_12, type, sP0: ('Nat_0()' * 'list_0()') > $o).
tff(pred_def_13, type, sP1: ('list_0()' * 'Nat_0()') > $o).
tff(f83,plain,(
  $false),
  inference(unit_resulting_resolution,[],[f65,f39,f60,f58])).
tff(f58,plain,(
  ( ! [X4 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'list_0()'] : (~sP0(X4,X1) | ~diseqNat_0(X4,X0) | sP1(X1,X0)) )),
  inference(cnf_transformation,[],[f58_D])).
tff(f58_D,plain,(
  ( ! [X0,X1] : (( ! [X4] : (~sP0(X4,X1) | ~diseqNat_0(X4,X0)) ) <=> ~sP1(X1,X0)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP1])])).
tff(f60,plain,(
  ( ! [X0 : 'list_0()'] : (sP0('Z_0',X0)) )),
  inference(unit_resulting_resolution,[],[f43,f56])).
tff(f56,plain,(
  ( ! [X4 : 'Nat_0()',X2 : 'list_0()',X1 : 'list_0()'] : (~rotate_0(X1,X4,X2) | sP0(X4,X1)) )),
  inference(cnf_transformation,[],[f56_D])).
tff(f56_D,plain,(
  ( ! [X1,X4] : (( ! [X2] : ~rotate_0(X1,X4,X2) ) <=> ~sP0(X4,X1)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP0])])).
tff(f43,plain,(
  ( ! [X0 : 'list_0()'] : (rotate_0(X0,'Z_0',X0)) )),
  inference(cnf_transformation,[],[f17])).
tff(f17,axiom,(
  ! [X0 : 'list_0()'] : rotate_0(X0,'Z_0',X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0.smt2',unknown)).
tff(f39,plain,(
  ( ! [X0 : 'Nat_0()'] : (diseqNat_0('Z_0','S_0'(X0))) )),
  inference(cnf_transformation,[],[f5])).
tff(f5,axiom,(
  ! [X0 : 'Nat_0()'] : diseqNat_0('Z_0','S_0'(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0.smt2',unknown)).
tff(f65,plain,(
  ( ! [X0 : 'Nat_0()'] : (~sP1(nil_0,'S_0'(X0))) )),
  inference(unit_resulting_resolution,[],[f44,f59])).
tff(f59,plain,(
  ( ! [X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~rotate_0(X1,X0,X3) | ~sP1(X1,X0)) )),
  inference(general_splitting,[],[f57,f58_D])).
tff(f57,plain,(
  ( ! [X4 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~diseqNat_0(X4,X0) | ~rotate_0(X1,X0,X3) | ~sP0(X4,X1)) )),
  inference(general_splitting,[],[f54,f56_D])).
tff(f54,plain,(
  ( ! [X4 : 'Nat_0()',X2 : 'list_0()',X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~diseqNat_0(X4,X0) | ~rotate_0(X1,X4,X2) | ~rotate_0(X1,X0,X3)) )),
  inference(cnf_transformation,[],[f33])).
tff(f33,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()',X4 : 'Nat_0()'] : (~diseqNat_0(X4,X0) | ~rotate_0(X1,X4,X2) | ~rotate_0(X1,X0,X3))),
  inference(ennf_transformation,[],[f27])).
tff(f27,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()',X4 : 'Nat_0()'] : ~(diseqNat_0(X4,X0) & rotate_0(X1,X4,X2) & rotate_0(X1,X0,X3))),
  inference(true_and_false_elimination,[],[f26])).
tff(f26,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()',X4 : 'Nat_0()'] : ((diseqNat_0(X4,X0) & rotate_0(X1,X4,X2) & rotate_0(X1,X0,X3)) => $false)),
  inference(rectify,[],[f20])).
tff(f20,axiom,(
  ! [X2 : 'Nat_0()',X0 : 'list_0()',X4 : 'list_0()',X3 : 'list_0()',X1 : 'Nat_0()'] : ((diseqNat_0(X1,X2) & rotate_0(X0,X1,X4) & rotate_0(X0,X2,X3)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0.smt2',unknown)).
tff(f44,plain,(
  ( ! [X0 : 'Nat_0()'] : (rotate_0(nil_0,'S_0'(X0),nil_0)) )),
  inference(cnf_transformation,[],[f19])).
tff(f19,axiom,(
  ! [X0 : 'Nat_0()'] : rotate_0(nil_0,'S_0'(X0),nil_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_inj0.smt2',unknown)).
