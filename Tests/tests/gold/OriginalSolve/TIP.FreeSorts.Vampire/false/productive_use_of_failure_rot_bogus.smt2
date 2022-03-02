2
12416
40
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
tff(f178,plain,(
  $false),
  inference(unit_resulting_resolution,[],[f44,f80,f99,f56])).
tff(f56,plain,(
  ( ! [X4 : 'list_0()',X2 : 'Nat_0()',X0 : 'list_0()',X3 : 'list_0()',X1 : 'Nat_0()'] : (~x_0(X3,X0,cons_0(X1,nil_0)) | rotate_0(X4,'S_0'(X2),cons_0(X1,X0)) | ~rotate_0(X4,X2,X3)) )),
  inference(cnf_transformation,[],[f36])).
tff(f36,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'list_0()',X4 : 'list_0()'] : (rotate_0(X4,'S_0'(X2),cons_0(X1,X0)) | ~x_0(X3,X0,cons_0(X1,nil_0)) | ~rotate_0(X4,X2,X3))),
  inference(flattening,[],[f35])).
tff(f35,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'list_0()',X4 : 'list_0()'] : (rotate_0(X4,'S_0'(X2),cons_0(X1,X0)) | (~x_0(X3,X0,cons_0(X1,nil_0)) | ~rotate_0(X4,X2,X3)))),
  inference(ennf_transformation,[],[f29])).
tff(f29,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'list_0()',X4 : 'list_0()'] : ((x_0(X3,X0,cons_0(X1,nil_0)) & rotate_0(X4,X2,X3)) => rotate_0(X4,'S_0'(X2),cons_0(X1,X0)))),
  inference(rectify,[],[f18])).
tff(f18,axiom,(
  ! [X3 : 'list_0()',X2 : 'Nat_0()',X4 : 'Nat_0()',X0 : 'list_0()',X1 : 'list_0()'] : ((x_0(X0,X3,cons_0(X2,nil_0)) & rotate_0(X1,X4,X0)) => rotate_0(X1,'S_0'(X4),cons_0(X2,X3)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_bogus.smt2',unknown)).
tff(f99,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'list_0()'] : (x_0(cons_0(X0,X1),cons_0(X0,nil_0),X1)) )),
  inference(unit_resulting_resolution,[],[f43,f55])).
tff(f55,plain,(
  ( ! [X2 : 'list_0()',X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (x_0(cons_0(X0,X2),cons_0(X0,X1),X3) | ~x_0(X2,X1,X3)) )),
  inference(cnf_transformation,[],[f34])).
tff(f34,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()'] : (x_0(cons_0(X0,X2),cons_0(X0,X1),X3) | ~x_0(X2,X1,X3))),
  inference(ennf_transformation,[],[f28])).
tff(f28,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()'] : (x_0(X2,X1,X3) => x_0(cons_0(X0,X2),cons_0(X0,X1),X3))),
  inference(rectify,[],[f15])).
tff(f15,axiom,(
  ! [X1 : 'Nat_0()',X2 : 'list_0()',X0 : 'list_0()',X3 : 'list_0()'] : (x_0(X0,X2,X3) => x_0(cons_0(X1,X0),cons_0(X1,X2),X3))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_bogus.smt2',unknown)).
tff(f43,plain,(
  ( ! [X0 : 'list_0()'] : (x_0(X0,nil_0,X0)) )),
  inference(cnf_transformation,[],[f16])).
tff(f16,axiom,(
  ! [X0 : 'list_0()'] : x_0(X0,nil_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_bogus.smt2',unknown)).
tff(f80,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'list_0()',X3 : 'list_0()',X1 : 'Nat_0()'] : (~rotate_0(cons_0('Z_0',X0),X1,cons_0('S_0'(X2),X3))) )),
  inference(unit_resulting_resolution,[],[f70,f52])).
tff(f52,plain,(
  ( ! [X2 : 'list_0()',X0 : 'list_0()',X1 : 'Nat_0()'] : (~rotate_0(X2,X1,X0) | ~diseqlist_0(X0,X2)) )),
  inference(cnf_transformation,[],[f31])).
tff(f31,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'list_0()'] : (~diseqlist_0(X0,X2) | ~rotate_0(X2,X1,X0))),
  inference(ennf_transformation,[],[f25])).
tff(f25,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'list_0()'] : ~(diseqlist_0(X0,X2) & rotate_0(X2,X1,X0))),
  inference(true_and_false_elimination,[],[f24])).
tff(f24,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'list_0()'] : ((diseqlist_0(X0,X2) & rotate_0(X2,X1,X0)) => $false)),
  inference(rectify,[],[f20])).
tff(f20,axiom,(
  ! [X2 : 'list_0()',X1 : 'Nat_0()',X0 : 'list_0()'] : ((diseqlist_0(X2,X0) & rotate_0(X0,X1,X2)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_bogus.smt2',unknown)).
tff(f70,plain,(
  ( ! [X2 : 'list_0()',X0 : 'Nat_0()',X1 : 'list_0()'] : (diseqlist_0(cons_0('S_0'(X0),X1),cons_0('Z_0',X2))) )),
  inference(unit_resulting_resolution,[],[f41,f53])).
tff(f53,plain,(
  ( ! [X2 : 'list_0()',X0 : 'list_0()',X3 : 'Nat_0()',X1 : 'Nat_0()'] : (diseqlist_0(cons_0(X1,X0),cons_0(X3,X2)) | ~diseqNat_0(X1,X3)) )),
  inference(cnf_transformation,[],[f32])).
tff(f32,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'list_0()',X3 : 'Nat_0()'] : (diseqlist_0(cons_0(X1,X0),cons_0(X3,X2)) | ~diseqNat_0(X1,X3))),
  inference(ennf_transformation,[],[f26])).
tff(f26,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()',X2 : 'list_0()',X3 : 'Nat_0()'] : (diseqNat_0(X1,X3) => diseqlist_0(cons_0(X1,X0),cons_0(X3,X2)))),
  inference(rectify,[],[f13])).
tff(f13,axiom,(
  ! [X1 : 'list_0()',X0 : 'Nat_0()',X3 : 'list_0()',X2 : 'Nat_0()'] : (diseqNat_0(X0,X2) => diseqlist_0(cons_0(X0,X1),cons_0(X2,X3)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_bogus.smt2',unknown)).
tff(f41,plain,(
  ( ! [X0 : 'Nat_0()'] : (diseqNat_0('S_0'(X0),'Z_0')) )),
  inference(cnf_transformation,[],[f4])).
tff(f4,axiom,(
  ! [X0 : 'Nat_0()'] : diseqNat_0('S_0'(X0),'Z_0')),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_bogus.smt2',unknown)).
tff(f44,plain,(
  ( ! [X0 : 'list_0()'] : (rotate_0(X0,'Z_0',X0)) )),
  inference(cnf_transformation,[],[f17])).
tff(f17,axiom,(
  ! [X0 : 'list_0()'] : rotate_0(X0,'Z_0',X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/productive_use_of_failure_rot_bogus.smt2',unknown)).
