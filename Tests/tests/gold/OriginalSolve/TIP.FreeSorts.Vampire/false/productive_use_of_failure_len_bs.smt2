2
12008
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
tff(pred_def_12, type, sP0: ('Nat_0()' * 'list_0()') > $o).
tff(pred_def_13, type, sP1: ('list_0()' * 'list_0()') > $o).
tff(f78,plain,(
  $false),
  inference(unit_resulting_resolution,[],[f56,f64,f66,f54])).
tff(f54,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'list_0()',X3 : 'list_0()'] : (~sP0(X2,X0) | ~length_0(X2,X3) | sP1(X3,X0)) )),
  inference(cnf_transformation,[],[f54_D])).
tff(f54_D,plain,(
  ( ! [X0,X3] : (( ! [X2] : (~sP0(X2,X0) | ~length_0(X2,X3)) ) <=> ~sP1(X3,X0)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP1])])).
tff(f66,plain,(
  ( ! [X0 : 'Nat_0()'] : (sP0('S_0'(X0),nil_0)) )),
  inference(unit_resulting_resolution,[],[f38,f35,f52])).
tff(f52,plain,(
  ( ! [X4 : 'Nat_0()',X2 : 'Nat_0()',X0 : 'list_0()'] : (~length_0(X4,X0) | ~diseqNat_0(X2,X4) | sP0(X2,X0)) )),
  inference(cnf_transformation,[],[f52_D])).
tff(f52_D,plain,(
  ( ! [X0,X2] : (( ! [X4] : (~length_0(X4,X0) | ~diseqNat_0(X2,X4)) ) <=> ~sP0(X2,X0)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP0])])).
tff(f35,plain,(
  length_0('Z_0',nil_0)),
  inference(cnf_transformation,[],[f16])).
tff(f16,axiom,(
  length_0('Z_0',nil_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_len_bs.smt2',unknown)).
tff(f38,plain,(
  ( ! [X0 : 'Nat_0()'] : (diseqNat_0('S_0'(X0),'Z_0')) )),
  inference(cnf_transformation,[],[f4])).
tff(f4,axiom,(
  ! [X0 : 'Nat_0()'] : diseqNat_0('S_0'(X0),'Z_0')),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_len_bs.smt2',unknown)).
tff(f64,plain,(
  ( ! [X0 : 'Nat_0()'] : (length_0('S_0'('Z_0'),cons_0(X0,nil_0))) )),
  inference(unit_resulting_resolution,[],[f35,f47])).
tff(f47,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'list_0()'] : (length_0('S_0'(X0),cons_0(X2,X1)) | ~length_0(X0,X1)) )),
  inference(cnf_transformation,[],[f28])).
tff(f28,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()'] : (length_0('S_0'(X0),cons_0(X2,X1)) | ~length_0(X0,X1))),
  inference(ennf_transformation,[],[f21])).
tff(f21,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()'] : (length_0(X0,X1) => length_0('S_0'(X0),cons_0(X2,X1)))),
  inference(rectify,[],[f15])).
tff(f15,axiom,(
  ! [X0 : 'Nat_0()',X2 : 'list_0()',X1 : 'Nat_0()'] : (length_0(X0,X2) => length_0('S_0'(X0),cons_0(X1,X2)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_len_bs.smt2',unknown)).
tff(f56,plain,(
  ( ! [X0 : 'list_0()'] : (~sP1(X0,nil_0)) )),
  inference(unit_resulting_resolution,[],[f40,f55])).
tff(f55,plain,(
  ( ! [X0 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~x_1(X3,X0,X1) | ~sP1(X3,X0)) )),
  inference(general_splitting,[],[f53,f54_D])).
tff(f53,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~x_1(X3,X0,X1) | ~length_0(X2,X3) | ~sP0(X2,X0)) )),
  inference(general_splitting,[],[f51,f52_D])).
tff(f51,plain,(
  ( ! [X4 : 'Nat_0()',X2 : 'Nat_0()',X0 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~diseqNat_0(X2,X4) | ~x_1(X3,X0,X1) | ~length_0(X2,X3) | ~length_0(X4,X0)) )),
  inference(cnf_transformation,[],[f32])).
tff(f32,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()',X4 : 'Nat_0()'] : (~diseqNat_0(X2,X4) | ~x_1(X3,X0,X1) | ~length_0(X2,X3) | ~length_0(X4,X0))),
  inference(ennf_transformation,[],[f26])).
tff(f26,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()',X4 : 'Nat_0()'] : ~(diseqNat_0(X2,X4) & x_1(X3,X0,X1) & length_0(X2,X3) & length_0(X4,X0))),
  inference(true_and_false_elimination,[],[f25])).
tff(f25,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()',X4 : 'Nat_0()'] : ((diseqNat_0(X2,X4) & x_1(X3,X0,X1) & length_0(X2,X3) & length_0(X4,X0)) => $false)),
  inference(rectify,[],[f19])).
tff(f19,axiom,(
  ! [X3 : 'list_0()',X4 : 'list_0()',X1 : 'Nat_0()',X0 : 'list_0()',X2 : 'Nat_0()'] : ((diseqNat_0(X1,X2) & x_1(X0,X3,X4) & length_0(X1,X0) & length_0(X2,X3)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_len_bs.smt2',unknown)).
tff(f40,plain,(
  ( ! [X0 : 'list_0()'] : (x_1(X0,nil_0,X0)) )),
  inference(cnf_transformation,[],[f18])).
tff(f18,axiom,(
  ! [X0 : 'list_0()'] : x_1(X0,nil_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_len_bs.smt2',unknown)).
