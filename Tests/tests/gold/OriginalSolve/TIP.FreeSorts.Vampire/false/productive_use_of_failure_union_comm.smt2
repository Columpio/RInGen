4
12680
40
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
tff(pred_def_17, type, eqNat_0: ('Bool_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_18, type, barbar_0: ('Bool_0()' * 'Bool_0()' * 'Bool_0()') > $o).
tff(pred_def_19, type, elem_0: ('Bool_0()' * 'Nat_0()' * 'list_0()') > $o).
tff(pred_def_20, type, union_0: ('list_0()' * 'list_0()' * 'list_0()') > $o).
tff(pred_def_21, type, sP0: ('Nat_0()' * 'list_0()') > $o).
tff(pred_def_22, type, sP1: ('Nat_0()' * 'list_0()' * 'Bool_0()' * 'Bool_0()') > $o).
tff(f588,plain,(
  $false),
  inference(subsumption_resolution,[],[f576,f468])).
tff(f468,plain,(
  ( ! [X0 : 'Nat_0()'] : (~union_0(cons_0(X0,nil_0),cons_0('Z_0',cons_0('Z_0',nil_0)),cons_0('Z_0',nil_0))) )),
  inference(unit_resulting_resolution,[],[f140,f96,f428,f218])).
tff(f218,plain,(
  ( ! [X4 : 'list_0()',X2 : 'list_0()',X0 : 'list_0()',X3 : 'Nat_0()',X1 : 'list_0()'] : (~union_0(X4,X2,cons_0(X3,X1)) | ~elem_0(true_0,X3,X2) | ~diseqlist_0(X0,X4) | ~union_0(X0,X1,X2)) )),
  inference(resolution,[],[f109,f110])).
tff(f110,plain,(
  ( ! [X2 : 'list_0()',X0 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~union_0(X3,X2,X1) | ~diseqlist_0(X3,X0) | ~union_0(X0,X1,X2)) )),
  inference(cnf_transformation,[],[f64])).
tff(f64,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()'] : (~diseqlist_0(X3,X0) | ~union_0(X3,X2,X1) | ~union_0(X0,X1,X2))),
  inference(ennf_transformation,[],[f54])).
tff(f54,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()'] : ~(diseqlist_0(X3,X0) & union_0(X3,X2,X1) & union_0(X0,X1,X2))),
  inference(true_and_false_elimination,[],[f53])).
tff(f53,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()'] : ((diseqlist_0(X3,X0) & union_0(X3,X2,X1) & union_0(X0,X1,X2)) => $false)),
  inference(rectify,[],[f44])).
tff(f44,axiom,(
  ! [X1 : 'list_0()',X3 : 'list_0()',X2 : 'list_0()',X0 : 'list_0()'] : ((diseqlist_0(X0,X1) & union_0(X0,X2,X3) & union_0(X1,X3,X2)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_union_comm.smt2',unknown)).
tff(f109,plain,(
  ( ! [X2 : 'list_0()',X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (union_0(X3,cons_0(X0,X1),X2) | ~union_0(X3,X1,X2) | ~elem_0(true_0,X0,X2)) )),
  inference(cnf_transformation,[],[f63])).
tff(f63,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()'] : (union_0(X3,cons_0(X0,X1),X2) | ~union_0(X3,X1,X2) | ~elem_0(true_0,X0,X2))),
  inference(flattening,[],[f62])).
tff(f62,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()'] : (union_0(X3,cons_0(X0,X1),X2) | (~union_0(X3,X1,X2) | ~elem_0(true_0,X0,X2)))),
  inference(ennf_transformation,[],[f52])).
tff(f52,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()'] : ((union_0(X3,X1,X2) & elem_0(true_0,X0,X2)) => union_0(X3,cons_0(X0,X1),X2))),
  inference(rectify,[],[f41])).
tff(f41,axiom,(
  ! [X1 : 'Nat_0()',X2 : 'list_0()',X3 : 'list_0()',X0 : 'list_0()'] : ((union_0(X0,X2,X3) & elem_0(true_0,X1,X3)) => union_0(X0,cons_0(X1,X2),X3))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_union_comm.smt2',unknown)).
tff(f428,plain,(
  elem_0(true_0,'Z_0',cons_0('Z_0',cons_0('Z_0',nil_0)))),
  inference(unit_resulting_resolution,[],[f89,f411,f115])).
tff(f115,plain,(
  ( ! [X4 : 'Nat_0()',X2 : 'list_0()',X0 : 'Bool_0()',X3 : 'Nat_0()',X1 : 'Bool_0()'] : (sP1(X3,X2,X1,X0) | ~eqNat_0(X1,X3,X4) | elem_0(X0,X3,cons_0(X4,X2))) )),
  inference(cnf_transformation,[],[f115_D])).
tff(f115_D,plain,(
  ( ! [X0,X1,X2,X3] : (( ! [X4] : (~eqNat_0(X1,X3,X4) | elem_0(X0,X3,cons_0(X4,X2))) ) <=> ~sP1(X3,X2,X1,X0)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP1])])).
tff(f411,plain,(
  ~sP1('Z_0',cons_0('Z_0',nil_0),true_0,true_0)),
  inference(unit_resulting_resolution,[],[f94,f367,f116])).
tff(f116,plain,(
  ( ! [X2 : 'list_0()',X0 : 'Bool_0()',X5 : 'Bool_0()',X3 : 'Nat_0()',X1 : 'Bool_0()'] : (~sP1(X3,X2,X1,X0) | ~barbar_0(X0,X1,X5) | ~elem_0(X5,X3,X2)) )),
  inference(general_splitting,[],[f112,f115_D])).
tff(f112,plain,(
  ( ! [X4 : 'Nat_0()',X2 : 'list_0()',X0 : 'Bool_0()',X5 : 'Bool_0()',X3 : 'Nat_0()',X1 : 'Bool_0()'] : (elem_0(X0,X3,cons_0(X4,X2)) | ~eqNat_0(X1,X3,X4) | ~elem_0(X5,X3,X2) | ~barbar_0(X0,X1,X5)) )),
  inference(cnf_transformation,[],[f68])).
tff(f68,plain,(
  ! [X0 : 'Bool_0()',X1 : 'Bool_0()',X2 : 'list_0()',X3 : 'Nat_0()',X4 : 'Nat_0()',X5 : 'Bool_0()'] : (elem_0(X0,X3,cons_0(X4,X2)) | ~eqNat_0(X1,X3,X4) | ~elem_0(X5,X3,X2) | ~barbar_0(X0,X1,X5))),
  inference(flattening,[],[f67])).
tff(f67,plain,(
  ! [X0 : 'Bool_0()',X1 : 'Bool_0()',X2 : 'list_0()',X3 : 'Nat_0()',X4 : 'Nat_0()',X5 : 'Bool_0()'] : (elem_0(X0,X3,cons_0(X4,X2)) | (~eqNat_0(X1,X3,X4) | ~elem_0(X5,X3,X2) | ~barbar_0(X0,X1,X5)))),
  inference(ennf_transformation,[],[f56])).
tff(f56,plain,(
  ! [X0 : 'Bool_0()',X1 : 'Bool_0()',X2 : 'list_0()',X3 : 'Nat_0()',X4 : 'Nat_0()',X5 : 'Bool_0()'] : ((eqNat_0(X1,X3,X4) & elem_0(X5,X3,X2) & barbar_0(X0,X1,X5)) => elem_0(X0,X3,cons_0(X4,X2)))),
  inference(rectify,[],[f39])).
tff(f39,axiom,(
  ! [X0 : 'Bool_0()',X1 : 'Bool_0()',X4 : 'list_0()',X5 : 'Nat_0()',X3 : 'Nat_0()',X2 : 'Bool_0()'] : ((eqNat_0(X1,X5,X3) & elem_0(X2,X5,X4) & barbar_0(X0,X1,X2)) => elem_0(X0,X5,cons_0(X3,X4)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_union_comm.smt2',unknown)).
tff(f367,plain,(
  elem_0(true_0,'Z_0',cons_0('Z_0',nil_0))),
  inference(unit_resulting_resolution,[],[f205,f89,f115])).
tff(f205,plain,(
  ( ! [X0 : 'Nat_0()'] : (~sP1(X0,nil_0,true_0,true_0)) )),
  inference(unit_resulting_resolution,[],[f95,f94,f116])).
tff(f95,plain,(
  ( ! [X0 : 'Nat_0()'] : (elem_0(false_0,X0,nil_0)) )),
  inference(cnf_transformation,[],[f40])).
tff(f40,axiom,(
  ! [X0 : 'Nat_0()'] : elem_0(false_0,X0,nil_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_union_comm.smt2',unknown)).
tff(f94,plain,(
  ( ! [X0 : 'Bool_0()'] : (barbar_0(true_0,true_0,X0)) )),
  inference(cnf_transformation,[],[f37])).
tff(f37,axiom,(
  ! [X0 : 'Bool_0()'] : barbar_0(true_0,true_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_union_comm.smt2',unknown)).
tff(f89,plain,(
  eqNat_0(true_0,'Z_0','Z_0')),
  inference(cnf_transformation,[],[f33])).
tff(f33,axiom,(
  eqNat_0(true_0,'Z_0','Z_0')),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_union_comm.smt2',unknown)).
tff(f96,plain,(
  ( ! [X0 : 'list_0()'] : (union_0(X0,nil_0,X0)) )),
  inference(cnf_transformation,[],[f43])).
tff(f43,axiom,(
  ! [X0 : 'list_0()'] : union_0(X0,nil_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_union_comm.smt2',unknown)).
tff(f140,plain,(
  ( ! [X2 : 'list_0()',X0 : 'Nat_0()',X3 : 'Nat_0()',X1 : 'Nat_0()'] : (diseqlist_0(cons_0(X0,cons_0(X1,X2)),cons_0(X3,nil_0))) )),
  inference(unit_resulting_resolution,[],[f101,f108])).
tff(f108,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'list_0()',X3 : 'Nat_0()',X1 : 'list_0()'] : (diseqlist_0(cons_0(X3,X0),cons_0(X2,X1)) | ~diseqlist_0(X0,X1)) )),
  inference(cnf_transformation,[],[f61])).
tff(f61,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'Nat_0()'] : (diseqlist_0(cons_0(X3,X0),cons_0(X2,X1)) | ~diseqlist_0(X0,X1))),
  inference(ennf_transformation,[],[f51])).
tff(f51,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'Nat_0()'] : (diseqlist_0(X0,X1) => diseqlist_0(cons_0(X3,X0),cons_0(X2,X1)))),
  inference(rectify,[],[f32])).
tff(f32,axiom,(
  ! [X1 : 'list_0()',X3 : 'list_0()',X2 : 'Nat_0()',X0 : 'Nat_0()'] : (diseqlist_0(X1,X3) => diseqlist_0(cons_0(X0,X1),cons_0(X2,X3)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_union_comm.smt2',unknown)).
tff(f101,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'list_0()'] : (diseqlist_0(cons_0(X0,X1),nil_0)) )),
  inference(cnf_transformation,[],[f30])).
tff(f30,axiom,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()'] : diseqlist_0(cons_0(X0,X1),nil_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_union_comm.smt2',unknown)).
tff(f576,plain,(
  union_0(cons_0('Z_0',nil_0),cons_0('Z_0',cons_0('Z_0',nil_0)),cons_0('Z_0',nil_0))),
  inference(unit_resulting_resolution,[],[f367,f410,f109])).
tff(f410,plain,(
  union_0(cons_0('Z_0',nil_0),cons_0('Z_0',nil_0),cons_0('Z_0',nil_0))),
  inference(unit_resulting_resolution,[],[f96,f367,f109])).
