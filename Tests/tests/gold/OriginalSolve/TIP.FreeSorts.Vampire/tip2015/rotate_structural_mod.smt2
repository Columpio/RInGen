8
14580
110
UNSAT
tff(type_def_5, type, 'Nat_1()': $tType).
tff(type_def_6, type, 'list_0()': $tType).
tff(type_def_7, type, 'Nat_0()': $tType).
tff(func_def_0, type, 'Z_11': 'Nat_1()').
tff(func_def_1, type, 'Z_12': ('Nat_1()') > 'Nat_1()').
tff(func_def_2, type, nil_0: 'list_0()').
tff(func_def_3, type, cons_0: ('Nat_1()' * 'list_0()') > 'list_0()').
tff(func_def_4, type, zero_0: 'Nat_0()').
tff(func_def_5, type, succ_0: ('Nat_0()') > 'Nat_0()').
tff(pred_def_1, type, diseqNat_1: ('Nat_1()' * 'Nat_1()') > $o).
tff(pred_def_2, type, unS_1: ('Nat_1()' * 'Nat_1()') > $o).
tff(pred_def_3, type, isZ_2: ('Nat_1()') > $o).
tff(pred_def_4, type, isZ_3: ('Nat_1()') > $o).
tff(pred_def_5, type, add_0: ('Nat_1()' * 'Nat_1()' * 'Nat_1()') > $o).
tff(pred_def_6, type, minus_1: ('Nat_1()' * 'Nat_1()' * 'Nat_1()') > $o).
tff(pred_def_7, type, le_0: ('Nat_1()' * 'Nat_1()') > $o).
tff(pred_def_8, type, ge_0: ('Nat_1()' * 'Nat_1()') > $o).
tff(pred_def_9, type, lt_0: ('Nat_1()' * 'Nat_1()') > $o).
tff(pred_def_10, type, gt_0: ('Nat_1()' * 'Nat_1()') > $o).
tff(pred_def_11, type, mult_0: ('Nat_1()' * 'Nat_1()' * 'Nat_1()') > $o).
tff(pred_def_12, type, div_0: ('Nat_1()' * 'Nat_1()' * 'Nat_1()') > $o).
tff(pred_def_13, type, mod_0: ('Nat_1()' * 'Nat_1()' * 'Nat_1()') > $o).
tff(pred_def_14, type, diseqlist_0: ('list_0()' * 'list_0()') > $o).
tff(pred_def_15, type, head_1: ('Nat_1()' * 'list_0()') > $o).
tff(pred_def_16, type, tail_1: ('list_0()' * 'list_0()') > $o).
tff(pred_def_17, type, isnil_0: ('list_0()') > $o).
tff(pred_def_18, type, iscons_0: ('list_0()') > $o).
tff(pred_def_19, type, diseqNat_0: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_20, type, p_1: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_21, type, iszero_0: ('Nat_0()') > $o).
tff(pred_def_22, type, issucc_0: ('Nat_0()') > $o).
tff(pred_def_23, type, take_0: ('list_0()' * 'Nat_0()' * 'list_0()') > $o).
tff(pred_def_24, type, plus_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_25, type, minus_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_26, type, length_0: ('Nat_0()' * 'list_0()') > $o).
tff(pred_def_27, type, go_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_28, type, modstructural_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_29, type, drop_0: ('list_0()' * 'Nat_0()' * 'list_0()') > $o).
tff(pred_def_30, type, x_11: ('list_0()' * 'list_0()' * 'list_0()') > $o).
tff(pred_def_31, type, rotate_0: ('list_0()' * 'Nat_0()' * 'list_0()') > $o).
tff(pred_def_32, type, sP0: ('list_0()' * 'Nat_0()') > $o).
tff(pred_def_33, type, sP1: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_34, type, sP2: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_35, type, sP3: ('Nat_0()' * 'Nat_0()' * 'list_0()') > $o).
tff(pred_def_36, type, sP4: ('Nat_0()' * 'list_0()' * 'list_0()') > $o).
tff(pred_def_37, type, sP5: ('list_0()' * 'Nat_0()' * 'list_0()') > $o).
tff(pred_def_38, type, sP6: ('Nat_0()' * 'list_0()' * 'Nat_0()') > $o).
tff(pred_def_39, type, sP7: ('list_0()' * 'list_0()' * 'Nat_0()') > $o).
tff(f4530,plain,(
  $false),
  inference(unit_resulting_resolution,[],[f670,f917,f915,f4486,f223])).
tff(f223,plain,(
  ( ! [X6 : 'Nat_0()',X7 : 'list_0()',X5 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~sP7(X1,X7,X6) | ~sP4(X6,X7,X3) | ~sP5(X5,X6,X7) | ~x_11(X3,X5,X1)) )),
  inference(general_splitting,[],[f221,f222_D])).
tff(f222,plain,(
  ( ! [X6 : 'Nat_0()',X2 : 'Nat_0()',X7 : 'list_0()',X1 : 'list_0()'] : (~sP6(X2,X7,X6) | ~take_0(X1,X2,X7) | sP7(X1,X7,X6)) )),
  inference(cnf_transformation,[],[f222_D])).
tff(f222_D,plain,(
  ( ! [X6,X7,X1] : (( ! [X2] : (~sP6(X2,X7,X6) | ~take_0(X1,X2,X7)) ) <=> ~sP7(X1,X7,X6)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
tff(f221,plain,(
  ( ! [X6 : 'Nat_0()',X2 : 'Nat_0()',X7 : 'list_0()',X5 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()'] : (~take_0(X1,X2,X7) | ~x_11(X3,X5,X1) | ~sP4(X6,X7,X3) | ~sP5(X5,X6,X7) | ~sP6(X2,X7,X6)) )),
  inference(general_splitting,[],[f219,f220_D])).
tff(f220,plain,(
  ( ! [X6 : 'Nat_0()',X2 : 'Nat_0()',X7 : 'list_0()',X9 : 'Nat_0()'] : (~modstructural_0(X2,X6,X9) | ~length_0(X9,X7) | sP6(X2,X7,X6)) )),
  inference(cnf_transformation,[],[f220_D])).
tff(f220_D,plain,(
  ( ! [X6,X7,X2] : (( ! [X9] : (~modstructural_0(X2,X6,X9) | ~length_0(X9,X7)) ) <=> ~sP6(X2,X7,X6)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
tff(f219,plain,(
  ( ! [X6 : 'Nat_0()',X2 : 'Nat_0()',X7 : 'list_0()',X5 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()',X9 : 'Nat_0()'] : (~length_0(X9,X7) | ~modstructural_0(X2,X6,X9) | ~take_0(X1,X2,X7) | ~x_11(X3,X5,X1) | ~sP4(X6,X7,X3) | ~sP5(X5,X6,X7)) )),
  inference(general_splitting,[],[f217,f218_D])).
tff(f218,plain,(
  ( ! [X6 : 'Nat_0()',X8 : 'Nat_0()',X7 : 'list_0()',X5 : 'list_0()'] : (~sP3(X6,X8,X7) | ~drop_0(X5,X8,X7) | sP5(X5,X6,X7)) )),
  inference(cnf_transformation,[],[f218_D])).
tff(f218_D,plain,(
  ( ! [X7,X6,X5] : (( ! [X8] : (~sP3(X6,X8,X7) | ~drop_0(X5,X8,X7)) ) <=> ~sP5(X5,X6,X7)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
tff(f217,plain,(
  ( ! [X6 : 'Nat_0()',X2 : 'Nat_0()',X8 : 'Nat_0()',X7 : 'list_0()',X5 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()',X9 : 'Nat_0()'] : (~drop_0(X5,X8,X7) | ~length_0(X9,X7) | ~modstructural_0(X2,X6,X9) | ~take_0(X1,X2,X7) | ~x_11(X3,X5,X1) | ~sP3(X6,X8,X7) | ~sP4(X6,X7,X3)) )),
  inference(general_splitting,[],[f215,f216_D])).
tff(f216,plain,(
  ( ! [X6 : 'Nat_0()',X0 : 'list_0()',X7 : 'list_0()',X3 : 'list_0()'] : (~rotate_0(X0,X6,X7) | ~diseqlist_0(X0,X3) | sP4(X6,X7,X3)) )),
  inference(cnf_transformation,[],[f216_D])).
tff(f216_D,plain,(
  ( ! [X3,X7,X6] : (( ! [X0] : (~rotate_0(X0,X6,X7) | ~diseqlist_0(X0,X3)) ) <=> ~sP4(X6,X7,X3)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
tff(f215,plain,(
  ( ! [X6 : 'Nat_0()',X2 : 'Nat_0()',X0 : 'list_0()',X8 : 'Nat_0()',X7 : 'list_0()',X5 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()',X9 : 'Nat_0()'] : (~diseqlist_0(X0,X3) | ~rotate_0(X0,X6,X7) | ~drop_0(X5,X8,X7) | ~length_0(X9,X7) | ~modstructural_0(X2,X6,X9) | ~take_0(X1,X2,X7) | ~x_11(X3,X5,X1) | ~sP3(X6,X8,X7)) )),
  inference(general_splitting,[],[f207,f214_D])).
tff(f214,plain,(
  ( ! [X6 : 'Nat_0()',X4 : 'Nat_0()',X8 : 'Nat_0()',X7 : 'list_0()'] : (~modstructural_0(X8,X6,X4) | ~length_0(X4,X7) | sP3(X6,X8,X7)) )),
  inference(cnf_transformation,[],[f214_D])).
tff(f214_D,plain,(
  ( ! [X7,X8,X6] : (( ! [X4] : (~modstructural_0(X8,X6,X4) | ~length_0(X4,X7)) ) <=> ~sP3(X6,X8,X7)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
tff(f207,plain,(
  ( ! [X6 : 'Nat_0()',X4 : 'Nat_0()',X2 : 'Nat_0()',X0 : 'list_0()',X8 : 'Nat_0()',X7 : 'list_0()',X5 : 'list_0()',X3 : 'list_0()',X1 : 'list_0()',X9 : 'Nat_0()'] : (~diseqlist_0(X0,X3) | ~rotate_0(X0,X6,X7) | ~length_0(X4,X7) | ~modstructural_0(X8,X6,X4) | ~drop_0(X5,X8,X7) | ~length_0(X9,X7) | ~modstructural_0(X2,X6,X9) | ~take_0(X1,X2,X7) | ~x_11(X3,X5,X1)) )),
  inference(cnf_transformation,[],[f140])).
tff(f140,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()',X4 : 'Nat_0()',X5 : 'list_0()',X6 : 'Nat_0()',X7 : 'list_0()',X8 : 'Nat_0()',X9 : 'Nat_0()'] : (~diseqlist_0(X0,X3) | ~rotate_0(X0,X6,X7) | ~length_0(X4,X7) | ~modstructural_0(X8,X6,X4) | ~drop_0(X5,X8,X7) | ~length_0(X9,X7) | ~modstructural_0(X2,X6,X9) | ~take_0(X1,X2,X7) | ~x_11(X3,X5,X1))),
  inference(ennf_transformation,[],[f104])).
tff(f104,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()',X4 : 'Nat_0()',X5 : 'list_0()',X6 : 'Nat_0()',X7 : 'list_0()',X8 : 'Nat_0()',X9 : 'Nat_0()'] : ~(diseqlist_0(X0,X3) & rotate_0(X0,X6,X7) & length_0(X4,X7) & modstructural_0(X8,X6,X4) & drop_0(X5,X8,X7) & length_0(X9,X7) & modstructural_0(X2,X6,X9) & take_0(X1,X2,X7) & x_11(X3,X5,X1))),
  inference(true_and_false_elimination,[],[f103])).
tff(f103,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'Nat_0()',X3 : 'list_0()',X4 : 'Nat_0()',X5 : 'list_0()',X6 : 'Nat_0()',X7 : 'list_0()',X8 : 'Nat_0()',X9 : 'Nat_0()'] : ((diseqlist_0(X0,X3) & rotate_0(X0,X6,X7) & length_0(X4,X7) & modstructural_0(X8,X6,X4) & drop_0(X5,X8,X7) & length_0(X9,X7) & modstructural_0(X2,X6,X9) & take_0(X1,X2,X7) & x_11(X3,X5,X1)) => $false)),
  inference(rectify,[],[f67])).
tff(f67,axiom,(
  ! [X0 : 'list_0()',X6 : 'list_0()',X5 : 'Nat_0()',X7 : 'list_0()',X1 : 'Nat_0()',X3 : 'list_0()',X8 : 'Nat_0()',X9 : 'list_0()',X2 : 'Nat_0()',X4 : 'Nat_0()'] : ((diseqlist_0(X0,X7) & rotate_0(X0,X8,X9) & length_0(X1,X9) & modstructural_0(X2,X8,X1) & drop_0(X3,X2,X9) & length_0(X4,X9) & modstructural_0(X5,X8,X4) & take_0(X6,X5,X9) & x_11(X7,X3,X6)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f4486,plain,(
  ( ! [X2 : 'list_0()',X0 : 'Nat_1()',X1 : 'Nat_1()'] : (sP4(succ_0(zero_0),cons_0(X0,cons_0('Z_11',nil_0)),cons_0('Z_12'(X1),X2))) )),
  inference(unit_resulting_resolution,[],[f318,f4223,f216])).
tff(f4223,plain,(
  ( ! [X0 : 'Nat_1()',X1 : 'Nat_1()'] : (rotate_0(cons_0(X0,cons_0(X1,nil_0)),succ_0(zero_0),cons_0(X1,cons_0(X0,nil_0)))) )),
  inference(unit_resulting_resolution,[],[f164,f669,f205])).
tff(f205,plain,(
  ( ! [X4 : 'Nat_0()',X2 : 'list_0()',X0 : 'list_0()',X3 : 'Nat_1()',X1 : 'list_0()'] : (~x_11(X2,X0,cons_0(X3,nil_0)) | rotate_0(X1,succ_0(X4),cons_0(X3,X0)) | ~rotate_0(X1,X4,X2)) )),
  inference(cnf_transformation,[],[f138])).
tff(f138,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'Nat_1()',X4 : 'Nat_0()'] : (rotate_0(X1,succ_0(X4),cons_0(X3,X0)) | ~x_11(X2,X0,cons_0(X3,nil_0)) | ~rotate_0(X1,X4,X2))),
  inference(flattening,[],[f137])).
tff(f137,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'Nat_1()',X4 : 'Nat_0()'] : (rotate_0(X1,succ_0(X4),cons_0(X3,X0)) | (~x_11(X2,X0,cons_0(X3,nil_0)) | ~rotate_0(X1,X4,X2)))),
  inference(ennf_transformation,[],[f100])).
tff(f100,plain,(
  ! [X0 : 'list_0()',X1 : 'list_0()',X2 : 'list_0()',X3 : 'Nat_1()',X4 : 'Nat_0()'] : ((x_11(X2,X0,cons_0(X3,nil_0)) & rotate_0(X1,X4,X2)) => rotate_0(X1,succ_0(X4),cons_0(X3,X0)))),
  inference(rectify,[],[f60])).
tff(f60,axiom,(
  ! [X3 : 'list_0()',X0 : 'list_0()',X1 : 'list_0()',X2 : 'Nat_1()',X4 : 'Nat_0()'] : ((x_11(X1,X3,cons_0(X2,nil_0)) & rotate_0(X0,X4,X1)) => rotate_0(X0,succ_0(X4),cons_0(X2,X3)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f669,plain,(
  ( ! [X0 : 'Nat_1()',X1 : 'list_0()'] : (x_11(cons_0(X0,X1),cons_0(X0,nil_0),X1)) )),
  inference(unit_resulting_resolution,[],[f162,f196])).
tff(f196,plain,(
  ( ! [X2 : 'list_0()',X0 : 'list_0()',X3 : 'list_0()',X1 : 'Nat_1()'] : (x_11(cons_0(X1,X2),cons_0(X1,X3),X0) | ~x_11(X2,X3,X0)) )),
  inference(cnf_transformation,[],[f124])).
tff(f124,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_1()',X2 : 'list_0()',X3 : 'list_0()'] : (x_11(cons_0(X1,X2),cons_0(X1,X3),X0) | ~x_11(X2,X3,X0))),
  inference(ennf_transformation,[],[f92])).
tff(f92,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_1()',X2 : 'list_0()',X3 : 'list_0()'] : (x_11(X2,X3,X0) => x_11(cons_0(X1,X2),cons_0(X1,X3),X0))),
  inference(rectify,[],[f58])).
tff(f58,axiom,(
  ! [X3 : 'list_0()',X1 : 'Nat_1()',X0 : 'list_0()',X2 : 'list_0()'] : (x_11(X0,X2,X3) => x_11(cons_0(X1,X0),cons_0(X1,X2),X3))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f162,plain,(
  ( ! [X0 : 'list_0()'] : (x_11(X0,nil_0,X0)) )),
  inference(cnf_transformation,[],[f59])).
tff(f59,axiom,(
  ! [X0 : 'list_0()'] : x_11(X0,nil_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f164,plain,(
  ( ! [X0 : 'list_0()'] : (rotate_0(X0,zero_0,X0)) )),
  inference(cnf_transformation,[],[f62])).
tff(f62,axiom,(
  ! [X0 : 'list_0()'] : rotate_0(X0,zero_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f318,plain,(
  ( ! [X2 : 'list_0()',X0 : 'list_0()',X1 : 'Nat_1()'] : (diseqlist_0(cons_0('Z_11',X0),cons_0('Z_12'(X1),X2))) )),
  inference(unit_resulting_resolution,[],[f151,f194])).
tff(f194,plain,(
  ( ! [X2 : 'Nat_1()',X0 : 'Nat_1()',X3 : 'list_0()',X1 : 'list_0()'] : (diseqlist_0(cons_0(X2,X3),cons_0(X0,X1)) | ~diseqNat_1(X2,X0)) )),
  inference(cnf_transformation,[],[f122])).
tff(f122,plain,(
  ! [X0 : 'Nat_1()',X1 : 'list_0()',X2 : 'Nat_1()',X3 : 'list_0()'] : (diseqlist_0(cons_0(X2,X3),cons_0(X0,X1)) | ~diseqNat_1(X2,X0))),
  inference(ennf_transformation,[],[f90])).
tff(f90,plain,(
  ! [X0 : 'Nat_1()',X1 : 'list_0()',X2 : 'Nat_1()',X3 : 'list_0()'] : (diseqNat_1(X2,X0) => diseqlist_0(cons_0(X2,X3),cons_0(X0,X1)))),
  inference(rectify,[],[f31])).
tff(f31,axiom,(
  ! [X2 : 'Nat_1()',X3 : 'list_0()',X0 : 'Nat_1()',X1 : 'list_0()'] : (diseqNat_1(X0,X2) => diseqlist_0(cons_0(X0,X1),cons_0(X2,X3)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f151,plain,(
  ( ! [X0 : 'Nat_1()'] : (diseqNat_1('Z_11','Z_12'(X0))) )),
  inference(cnf_transformation,[],[f4])).
tff(f4,axiom,(
  ! [X0 : 'Nat_1()'] : diseqNat_1('Z_11','Z_12'(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f915,plain,(
  ( ! [X0 : 'Nat_1()',X1 : 'Nat_1()'] : (sP7(nil_0,cons_0(X0,cons_0(X1,nil_0)),succ_0(zero_0))) )),
  inference(unit_resulting_resolution,[],[f159,f885,f222])).
tff(f885,plain,(
  ( ! [X0 : 'Nat_1()',X1 : 'Nat_1()'] : (sP6(zero_0,cons_0(X0,cons_0(X1,nil_0)),succ_0(zero_0))) )),
  inference(unit_resulting_resolution,[],[f465,f883,f220])).
tff(f883,plain,(
  modstructural_0(zero_0,succ_0(zero_0),succ_0(succ_0(zero_0)))),
  inference(unit_resulting_resolution,[],[f855,f191])).
tff(f191,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (~go_0(X0,X2,zero_0,X1) | modstructural_0(X0,X2,X1)) )),
  inference(cnf_transformation,[],[f119])).
tff(f119,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (modstructural_0(X0,X2,X1) | ~go_0(X0,X2,zero_0,X1))),
  inference(ennf_transformation,[],[f87])).
tff(f87,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (go_0(X0,X2,zero_0,X1) => modstructural_0(X0,X2,X1))),
  inference(rectify,[],[f54])).
tff(f54,axiom,(
  ! [X0 : 'Nat_0()',X2 : 'Nat_0()',X1 : 'Nat_0()'] : (go_0(X0,X1,zero_0,X2) => modstructural_0(X0,X1,X2))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f855,plain,(
  go_0(zero_0,succ_0(zero_0),zero_0,succ_0(succ_0(zero_0)))),
  inference(unit_resulting_resolution,[],[f827,f193])).
tff(f193,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (~go_0(X2,X1,X0,succ_0(X0)) | go_0(X2,succ_0(X1),zero_0,succ_0(X0))) )),
  inference(cnf_transformation,[],[f121])).
tff(f121,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (go_0(X2,succ_0(X1),zero_0,succ_0(X0)) | ~go_0(X2,X1,X0,succ_0(X0)))),
  inference(ennf_transformation,[],[f89])).
tff(f89,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (go_0(X2,X1,X0,succ_0(X0)) => go_0(X2,succ_0(X1),zero_0,succ_0(X0)))),
  inference(rectify,[],[f50])).
tff(f50,axiom,(
  ! [X2 : 'Nat_0()',X1 : 'Nat_0()',X0 : 'Nat_0()'] : (go_0(X0,X1,X2,succ_0(X2)) => go_0(X0,succ_0(X1),zero_0,succ_0(X2)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f827,plain,(
  ( ! [X0 : 'Nat_0()'] : (go_0(zero_0,zero_0,succ_0(zero_0),succ_0(succ_0(X0)))) )),
  inference(unit_resulting_resolution,[],[f313,f192])).
tff(f192,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (go_0(X1,zero_0,succ_0(X2),succ_0(X0)) | ~minus_0(X1,succ_0(X0),succ_0(X2))) )),
  inference(cnf_transformation,[],[f120])).
tff(f120,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (go_0(X1,zero_0,succ_0(X2),succ_0(X0)) | ~minus_0(X1,succ_0(X0),succ_0(X2)))),
  inference(ennf_transformation,[],[f88])).
tff(f88,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (minus_0(X1,succ_0(X0),succ_0(X2)) => go_0(X1,zero_0,succ_0(X2),succ_0(X0)))),
  inference(rectify,[],[f51])).
tff(f51,axiom,(
  ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (minus_0(X0,succ_0(X2),succ_0(X1)) => go_0(X0,zero_0,succ_0(X1),succ_0(X2)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f313,plain,(
  ( ! [X0 : 'Nat_0()'] : (minus_0(zero_0,succ_0(succ_0(X0)),succ_0(zero_0))) )),
  inference(unit_resulting_resolution,[],[f169,f190])).
tff(f190,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (minus_0(X1,succ_0(X0),succ_0(X2)) | ~minus_0(X1,X0,X2)) )),
  inference(cnf_transformation,[],[f118])).
tff(f118,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (minus_0(X1,succ_0(X0),succ_0(X2)) | ~minus_0(X1,X0,X2))),
  inference(ennf_transformation,[],[f86])).
tff(f86,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (minus_0(X1,X0,X2) => minus_0(X1,succ_0(X0),succ_0(X2)))),
  inference(rectify,[],[f44])).
tff(f44,axiom,(
  ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (minus_0(X0,X2,X1) => minus_0(X0,succ_0(X2),succ_0(X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f169,plain,(
  ( ! [X0 : 'Nat_0()'] : (minus_0(zero_0,succ_0(X0),zero_0)) )),
  inference(cnf_transformation,[],[f45])).
tff(f45,axiom,(
  ! [X0 : 'Nat_0()'] : minus_0(zero_0,succ_0(X0),zero_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f465,plain,(
  ( ! [X0 : 'Nat_1()',X1 : 'Nat_1()'] : (length_0(succ_0(succ_0(zero_0)),cons_0(X0,cons_0(X1,nil_0)))) )),
  inference(unit_resulting_resolution,[],[f461,f208])).
tff(f208,plain,(
  ( ! [X2 : 'Nat_1()',X0 : 'Nat_0()',X3 : 'list_0()'] : (sP0(X3,X0) | length_0(X0,cons_0(X2,X3))) )),
  inference(cnf_transformation,[],[f208_D])).
tff(f208_D,plain,(
  ( ! [X0,X3] : (( ! [X2] : length_0(X0,cons_0(X2,X3)) ) <=> ~sP0(X3,X0)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP0])])).
tff(f461,plain,(
  ( ! [X0 : 'Nat_1()'] : (~sP0(cons_0(X0,nil_0),succ_0(succ_0(zero_0)))) )),
  inference(unit_resulting_resolution,[],[f284,f459,f209])).
tff(f209,plain,(
  ( ! [X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'Nat_0()'] : (~plus_0(X0,succ_0(zero_0),X1) | ~length_0(X1,X3) | ~sP0(X3,X0)) )),
  inference(general_splitting,[],[f204,f208_D])).
tff(f204,plain,(
  ( ! [X2 : 'Nat_1()',X0 : 'Nat_0()',X3 : 'list_0()',X1 : 'Nat_0()'] : (length_0(X0,cons_0(X2,X3)) | ~length_0(X1,X3) | ~plus_0(X0,succ_0(zero_0),X1)) )),
  inference(cnf_transformation,[],[f136])).
tff(f136,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_1()',X3 : 'list_0()'] : (length_0(X0,cons_0(X2,X3)) | ~length_0(X1,X3) | ~plus_0(X0,succ_0(zero_0),X1))),
  inference(flattening,[],[f135])).
tff(f135,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_1()',X3 : 'list_0()'] : (length_0(X0,cons_0(X2,X3)) | (~length_0(X1,X3) | ~plus_0(X0,succ_0(zero_0),X1)))),
  inference(ennf_transformation,[],[f47])).
tff(f47,axiom,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_1()',X3 : 'list_0()'] : ((length_0(X1,X3) & plus_0(X0,succ_0(zero_0),X1)) => length_0(X0,cons_0(X2,X3)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f459,plain,(
  ( ! [X0 : 'Nat_1()'] : (length_0(succ_0(zero_0),cons_0(X0,nil_0))) )),
  inference(unit_resulting_resolution,[],[f456,f208])).
tff(f456,plain,(
  ~sP0(nil_0,succ_0(zero_0))),
  inference(unit_resulting_resolution,[],[f144,f284,f209])).
tff(f144,plain,(
  length_0(zero_0,nil_0)),
  inference(cnf_transformation,[],[f48])).
tff(f48,axiom,(
  length_0(zero_0,nil_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f284,plain,(
  ( ! [X0 : 'Nat_0()'] : (plus_0(succ_0(X0),succ_0(zero_0),X0)) )),
  inference(unit_resulting_resolution,[],[f163,f189])).
tff(f189,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (plus_0(succ_0(X2),succ_0(X0),X1) | ~plus_0(X2,X0,X1)) )),
  inference(cnf_transformation,[],[f117])).
tff(f117,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (plus_0(succ_0(X2),succ_0(X0),X1) | ~plus_0(X2,X0,X1))),
  inference(ennf_transformation,[],[f85])).
tff(f85,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (plus_0(X2,X0,X1) => plus_0(succ_0(X2),succ_0(X0),X1))),
  inference(rectify,[],[f42])).
tff(f42,axiom,(
  ! [X1 : 'Nat_0()',X2 : 'Nat_0()',X0 : 'Nat_0()'] : (plus_0(X0,X1,X2) => plus_0(succ_0(X0),succ_0(X1),X2))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f163,plain,(
  ( ! [X0 : 'Nat_0()'] : (plus_0(X0,zero_0,X0)) )),
  inference(cnf_transformation,[],[f43])).
tff(f43,axiom,(
  ! [X0 : 'Nat_0()'] : plus_0(X0,zero_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f159,plain,(
  ( ! [X0 : 'list_0()'] : (take_0(nil_0,zero_0,X0)) )),
  inference(cnf_transformation,[],[f41])).
tff(f41,axiom,(
  ! [X0 : 'list_0()'] : take_0(nil_0,zero_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f917,plain,(
  ( ! [X0 : 'Nat_1()',X1 : 'Nat_1()'] : (sP5(cons_0(X0,cons_0(X1,nil_0)),succ_0(zero_0),cons_0(X0,cons_0(X1,nil_0)))) )),
  inference(unit_resulting_resolution,[],[f165,f886,f218])).
tff(f886,plain,(
  ( ! [X0 : 'Nat_1()',X1 : 'Nat_1()'] : (sP3(succ_0(zero_0),zero_0,cons_0(X0,cons_0(X1,nil_0)))) )),
  inference(unit_resulting_resolution,[],[f465,f883,f214])).
tff(f165,plain,(
  ( ! [X0 : 'list_0()'] : (drop_0(X0,zero_0,X0)) )),
  inference(cnf_transformation,[],[f57])).
tff(f57,axiom,(
  ! [X0 : 'list_0()'] : drop_0(X0,zero_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/rotate_structural_mod.smt2',unknown)).
tff(f670,plain,(
  ( ! [X2 : 'list_0()',X0 : 'Nat_1()',X1 : 'Nat_1()'] : (x_11(cons_0(X0,cons_0(X1,X2)),cons_0(X0,cons_0(X1,nil_0)),X2)) )),
  inference(unit_resulting_resolution,[],[f669,f196])).
