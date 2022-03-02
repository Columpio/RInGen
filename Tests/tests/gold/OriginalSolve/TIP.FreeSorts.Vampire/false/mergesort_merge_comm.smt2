4
13124
40
UNSAT
tff(type_def_5, type, 'Nat_0()': $tType).
tff(type_def_6, type, 'list_0()': $tType).
tff(func_def_0, type, 'Z_1': 'Nat_0()').
tff(func_def_1, type, 'Z_2': ('Nat_0()') > 'Nat_0()').
tff(func_def_2, type, nil_0: 'list_0()').
tff(func_def_3, type, cons_0: ('Nat_0()' * 'list_0()') > 'list_0()').
tff(pred_def_1, type, diseqNat_0: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_2, type, unS_1: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_3, type, isZ_2: ('Nat_0()') > $o).
tff(pred_def_4, type, isZ_3: ('Nat_0()') > $o).
tff(pred_def_5, type, add_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_6, type, minus_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_7, type, le_0: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_8, type, ge_0: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_9, type, lt_0: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_10, type, gt_0: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_11, type, mult_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_12, type, div_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_13, type, mod_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_14, type, diseqlist_0: ('list_0()' * 'list_0()') > $o).
tff(pred_def_15, type, head_1: ('Nat_0()' * 'list_0()') > $o).
tff(pred_def_16, type, tail_1: ('list_0()' * 'list_0()') > $o).
tff(pred_def_17, type, isnil_0: ('list_0()') > $o).
tff(pred_def_18, type, iscons_0: ('list_0()') > $o).
tff(pred_def_19, type, merge_0: ('list_0()' * 'list_0()' * 'list_0()') > $o).
tff(pred_def_20, type, sP0: ('list_0()' * 'list_0()') > $o).
tff(pred_def_21, type, sP1: ('list_0()' * 'list_0()') > $o).
tff(pred_def_22, type, sP2: ('list_0()' * 'list_0()') > $o).
tff(f957,plain,(
  $false),
  inference(unit_resulting_resolution,[],[f126,f628,f909,f113])).
tff(f113,plain,(
  ( ! [X4 : 'Nat_0()',X2 : 'list_0()',X0 : 'list_0()',X3 : 'Nat_0()',X1 : 'list_0()'] : (merge_0(cons_0(X4,X0),cons_0(X4,X2),cons_0(X3,X1)) | ~le_0(X4,X3) | ~merge_0(X0,X2,cons_0(X3,X1))) )),
  inference(cnf_transformation,[],[f75])).
tff(f75,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'Nat_0()',X4 : 'Nat_0()'] : (merge_0(cons_0(X4,X0),cons_0(X4,X2),cons_0(X3,X1)) | ~le_0(X4,X3) | ~merge_0(X0,X2,cons_0(X3,X1)))),
  inference(flattening,[],[f74])).
tff(f74,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'Nat_0()',X4 : 'Nat_0()'] : (merge_0(cons_0(X4,X0),cons_0(X4,X2),cons_0(X3,X1)) | (~le_0(X4,X3) | ~merge_0(X0,X2,cons_0(X3,X1))))),
  inference(ennf_transformation,[],[f53])).
tff(f53,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'Nat_0()',X4 : 'Nat_0()'] : ((le_0(X4,X3) & merge_0(X0,X2,cons_0(X3,X1))) => merge_0(cons_0(X4,X0),cons_0(X4,X2),cons_0(X3,X1)))),
  inference(rectify,[],[f33])).
tff(f33,axiom,(
  ! [X0 : 'list_0()',X2 : 'list_0()',X4 : 'list_0()',X1 : 'Nat_0()',X3 : 'Nat_0()'] : ((le_0(X3,X1) & merge_0(X0,X4,cons_0(X1,X2))) => merge_0(cons_0(X3,X0),cons_0(X3,X4),cons_0(X1,X2)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/mergesort_merge_comm.smt2',unknown)).
tff(f909,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~merge_0(cons_0(X0,cons_0('Z_1',X1)),cons_0('Z_2'(X2),X3),cons_0('Z_2'('Z_1'),nil_0))) )),
  inference(unit_resulting_resolution,[],[f162,f198,f629,f121])).
tff(f121,plain,(
  ( ! [X6 : 'list_0()',X4 : 'list_0()',X2 : 'list_0()',X1 : 'list_0()'] : (~merge_0(X6,X2,X1) | ~merge_0(X4,X1,X2) | ~diseqlist_0(X4,X6) | ~sP2(X2,X1)) )),
  inference(general_splitting,[],[f119,f120_D])).
tff(f120,plain,(
  ( ! [X2 : 'list_0()',X0 : 'list_0()',X1 : 'list_0()'] : (~sP1(X1,X0) | ~sP0(X2,X0) | sP2(X2,X1)) )),
  inference(cnf_transformation,[],[f120_D])).
tff(f120_D,plain,(
  ( ! [X1,X2] : (( ! [X0] : (~sP1(X1,X0) | ~sP0(X2,X0)) ) <=> ~sP2(X2,X1)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).
tff(f119,plain,(
  ( ! [X6 : 'list_0()',X4 : 'list_0()',X2 : 'list_0()',X0 : 'list_0()',X1 : 'list_0()'] : (~diseqlist_0(X4,X6) | ~merge_0(X4,X1,X2) | ~merge_0(X6,X2,X1) | ~sP0(X2,X0) | ~sP1(X1,X0)) )),
  inference(general_splitting,[],[f117,f118_D])).
tff(f118,plain,(
  ( ! [X0 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~merge_0(X3,X1,X0) | ~merge_0(X3,X0,X1) | sP1(X1,X0)) )),
  inference(cnf_transformation,[],[f118_D])).
tff(f118_D,plain,(
  ( ! [X0,X1] : (( ! [X3] : (~merge_0(X3,X1,X0) | ~merge_0(X3,X0,X1)) ) <=> ~sP1(X1,X0)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP1])])).
tff(f117,plain,(
  ( ! [X6 : 'list_0()',X4 : 'list_0()',X2 : 'list_0()',X0 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~diseqlist_0(X4,X6) | ~merge_0(X3,X0,X1) | ~merge_0(X3,X1,X0) | ~merge_0(X4,X1,X2) | ~merge_0(X6,X2,X1) | ~sP0(X2,X0)) )),
  inference(general_splitting,[],[f115,f116_D])).
tff(f116,plain,(
  ( ! [X2 : 'list_0()',X0 : 'list_0()',X5 : 'list_0()'] : (~merge_0(X5,X2,X0) | ~merge_0(X5,X0,X2) | sP0(X2,X0)) )),
  inference(cnf_transformation,[],[f116_D])).
tff(f116_D,plain,(
  ( ! [X0,X2] : (( ! [X5] : (~merge_0(X5,X2,X0) | ~merge_0(X5,X0,X2)) ) <=> ~sP0(X2,X0)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP0])])).
tff(f115,plain,(
  ( ! [X6 : 'list_0()',X4 : 'list_0()',X2 : 'list_0()',X0 : 'list_0()',X5 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~diseqlist_0(X4,X6) | ~merge_0(X3,X0,X1) | ~merge_0(X3,X1,X0) | ~merge_0(X5,X0,X2) | ~merge_0(X5,X2,X0) | ~merge_0(X4,X1,X2) | ~merge_0(X6,X2,X1)) )),
  inference(cnf_transformation,[],[f78])).
tff(f78,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()',X4 : 'list_0()',X5 : 'list_0()',X6 : 'list_0()'] : (~diseqlist_0(X4,X6) | ~merge_0(X3,X0,X1) | ~merge_0(X3,X1,X0) | ~merge_0(X5,X0,X2) | ~merge_0(X5,X2,X0) | ~merge_0(X4,X1,X2) | ~merge_0(X6,X2,X1))),
  inference(ennf_transformation,[],[f56])).
tff(f56,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()',X4 : 'list_0()',X5 : 'list_0()',X6 : 'list_0()'] : ~(diseqlist_0(X4,X6) & merge_0(X3,X0,X1) & merge_0(X3,X1,X0) & merge_0(X5,X0,X2) & merge_0(X5,X2,X0) & merge_0(X4,X1,X2) & merge_0(X6,X2,X1))),
  inference(true_and_false_elimination,[],[f55])).
tff(f55,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'list_0()',X4 : 'list_0()',X5 : 'list_0()',X6 : 'list_0()'] : ((diseqlist_0(X4,X6) & merge_0(X3,X0,X1) & merge_0(X3,X1,X0) & merge_0(X5,X0,X2) & merge_0(X5,X2,X0) & merge_0(X4,X1,X2) & merge_0(X6,X2,X1)) => $false)),
  inference(rectify,[],[f37])).
tff(f37,axiom,(
  ! [X4 : 'list_0()',X5 : 'list_0()',X6 : 'list_0()',X0 : 'list_0()',X2 : 'list_0()',X1 : 'list_0()',X3 : 'list_0()'] : ((diseqlist_0(X2,X3) & merge_0(X0,X4,X5) & merge_0(X0,X5,X4) & merge_0(X1,X4,X6) & merge_0(X1,X6,X4) & merge_0(X2,X5,X6) & merge_0(X3,X6,X5)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/mergesort_merge_comm.smt2',unknown)).
tff(f629,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'list_0()'] : (merge_0(cons_0('Z_2'('Z_1'),cons_0('Z_2'(X0),X1)),cons_0('Z_2'('Z_1'),nil_0),cons_0('Z_2'(X0),X1))) )),
  inference(unit_resulting_resolution,[],[f126,f92,f113])).
tff(f92,plain,(
  ( ! [X0 : 'list_0()'] : (merge_0(X0,nil_0,X0)) )),
  inference(cnf_transformation,[],[f36])).
tff(f36,axiom,(
  ! [X0 : 'list_0()'] : merge_0(X0,nil_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/mergesort_merge_comm.smt2',unknown)).
tff(f198,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (sP2(cons_0(X0,X1),cons_0(X2,X3))) )),
  inference(unit_resulting_resolution,[],[f180,f189,f120])).
tff(f189,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'list_0()'] : (sP1(cons_0(X0,X1),nil_0)) )),
  inference(unit_resulting_resolution,[],[f92,f98,f118])).
tff(f98,plain,(
  ( ! [X0 : 'list_0()',X1 : 'Nat_0()'] : (merge_0(cons_0(X1,X0),cons_0(X1,X0),nil_0)) )),
  inference(cnf_transformation,[],[f39])).
tff(f39,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()'] : merge_0(cons_0(X1,X0),cons_0(X1,X0),nil_0)),
  inference(rectify,[],[f35])).
tff(f35,axiom,(
  ! [X1 : 'list_0()',X0 : 'Nat_0()'] : merge_0(cons_0(X0,X1),cons_0(X0,X1),nil_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/mergesort_merge_comm.smt2',unknown)).
tff(f180,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'list_0()'] : (sP0(cons_0(X0,X1),nil_0)) )),
  inference(unit_resulting_resolution,[],[f92,f98,f116])).
tff(f162,plain,(
  ( ! [X4 : 'list_0()',X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'Nat_0()',X1 : 'list_0()'] : (diseqlist_0(cons_0(X0,cons_0('Z_1',X1)),cons_0(X2,cons_0('Z_2'(X3),X4)))) )),
  inference(unit_resulting_resolution,[],[f154,f109])).
tff(f109,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (diseqlist_0(cons_0(X2,X1),cons_0(X0,X3)) | ~diseqlist_0(X1,X3)) )),
  inference(cnf_transformation,[],[f67])).
tff(f67,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : (diseqlist_0(cons_0(X2,X1),cons_0(X0,X3)) | ~diseqlist_0(X1,X3))),
  inference(ennf_transformation,[],[f49])).
tff(f49,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : (diseqlist_0(X1,X3) => diseqlist_0(cons_0(X2,X1),cons_0(X0,X3)))),
  inference(rectify,[],[f32])).
tff(f32,axiom,(
  ! [X2 : 'Nat_0()',X1 : 'list_0()',X0 : 'Nat_0()',X3 : 'list_0()'] : (diseqlist_0(X1,X3) => diseqlist_0(cons_0(X0,X1),cons_0(X2,X3)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/mergesort_merge_comm.smt2',unknown)).
tff(f154,plain,(
  ( ! [X2 : 'list_0()',X0 : 'list_0()',X1 : 'Nat_0()'] : (diseqlist_0(cons_0('Z_1',X0),cons_0('Z_2'(X1),X2))) )),
  inference(unit_resulting_resolution,[],[f86,f108])).
tff(f108,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'list_0()'] : (diseqlist_0(cons_0(X2,X1),cons_0(X0,X3)) | ~diseqNat_0(X2,X0)) )),
  inference(cnf_transformation,[],[f66])).
tff(f66,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : (diseqlist_0(cons_0(X2,X1),cons_0(X0,X3)) | ~diseqNat_0(X2,X0))),
  inference(ennf_transformation,[],[f48])).
tff(f48,plain,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()'] : (diseqNat_0(X2,X0) => diseqlist_0(cons_0(X2,X1),cons_0(X0,X3)))),
  inference(rectify,[],[f31])).
tff(f31,axiom,(
  ! [X2 : 'Nat_0()',X1 : 'list_0()',X0 : 'Nat_0()',X3 : 'list_0()'] : (diseqNat_0(X0,X2) => diseqlist_0(cons_0(X0,X1),cons_0(X2,X3)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/mergesort_merge_comm.smt2',unknown)).
tff(f86,plain,(
  ( ! [X0 : 'Nat_0()'] : (diseqNat_0('Z_1','Z_2'(X0))) )),
  inference(cnf_transformation,[],[f4])).
tff(f4,axiom,(
  ! [X0 : 'Nat_0()'] : diseqNat_0('Z_1','Z_2'(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/mergesort_merge_comm.smt2',unknown)).
tff(f628,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'list_0()'] : (merge_0(cons_0('Z_1',cons_0(X0,X1)),cons_0('Z_1',nil_0),cons_0(X0,X1))) )),
  inference(unit_resulting_resolution,[],[f82,f92,f113])).
tff(f82,plain,(
  ( ! [X0 : 'Nat_0()'] : (le_0('Z_1',X0)) )),
  inference(cnf_transformation,[],[f11])).
tff(f11,axiom,(
  ! [X0 : 'Nat_0()'] : le_0('Z_1',X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/mergesort_merge_comm.smt2',unknown)).
tff(f126,plain,(
  ( ! [X0 : 'Nat_0()'] : (le_0('Z_2'('Z_1'),'Z_2'(X0))) )),
  inference(unit_resulting_resolution,[],[f82,f100])).
tff(f100,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (le_0('Z_2'(X1),'Z_2'(X0)) | ~le_0(X1,X0)) )),
  inference(cnf_transformation,[],[f58])).
tff(f58,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (le_0('Z_2'(X1),'Z_2'(X0)) | ~le_0(X1,X0))),
  inference(ennf_transformation,[],[f41])).
tff(f41,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (le_0(X1,X0) => le_0('Z_2'(X1),'Z_2'(X0)))),
  inference(rectify,[],[f12])).
tff(f12,axiom,(
  ! [X1 : 'Nat_0()',X0 : 'Nat_0()'] : (le_0(X0,X1) => le_0('Z_2'(X0),'Z_2'(X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/false/mergesort_merge_comm.smt2',unknown)).
