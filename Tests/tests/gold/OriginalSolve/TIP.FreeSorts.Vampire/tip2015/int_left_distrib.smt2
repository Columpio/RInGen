7
14924
220
UNSAT
tff(type_def_5, type, 'Sign_0()': $tType).
tff(type_def_6, type, 'Nat_0()': $tType).
tff(type_def_7, type, 'Integer_0()': $tType).
tff(func_def_0, type, 'Pos_0': 'Sign_0()').
tff(func_def_1, type, 'Neg_0': 'Sign_0()').
tff(func_def_2, type, zero_0: 'Nat_0()').
tff(func_def_3, type, succ_0: ('Nat_0()') > 'Nat_0()').
tff(func_def_4, type, 'P_1': ('Nat_0()') > 'Integer_0()').
tff(func_def_5, type, 'N_0': ('Nat_0()') > 'Integer_0()').
tff(pred_def_1, type, diseqSign_0: ('Sign_0()' * 'Sign_0()') > $o).
tff(pred_def_2, type, isPos_0: ('Sign_0()') > $o).
tff(pred_def_3, type, isNeg_0: ('Sign_0()') > $o).
tff(pred_def_4, type, diseqNat_0: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_5, type, p_2: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_6, type, iszero_0: ('Nat_0()') > $o).
tff(pred_def_7, type, issucc_0: ('Nat_0()') > $o).
tff(pred_def_8, type, diseqInteger_0: ('Integer_0()' * 'Integer_0()') > $o).
tff(pred_def_9, type, projP_1: ('Nat_0()' * 'Integer_0()') > $o).
tff(pred_def_10, type, projN_1: ('Nat_0()' * 'Integer_0()') > $o).
tff(pred_def_11, type, isP_0: ('Integer_0()') > $o).
tff(pred_def_12, type, isN_0: ('Integer_0()') > $o).
tff(pred_def_13, type, toInteger_0: ('Integer_0()' * 'Sign_0()' * 'Nat_0()') > $o).
tff(pred_def_14, type, sign_1: ('Sign_0()' * 'Integer_0()') > $o).
tff(pred_def_15, type, plus_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_16, type, times_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_17, type, opposite_0: ('Sign_0()' * 'Sign_0()') > $o).
tff(pred_def_18, type, timesSign_0: ('Sign_0()' * 'Sign_0()' * 'Sign_0()') > $o).
tff(pred_def_19, type, absVal_0: ('Nat_0()' * 'Integer_0()') > $o).
tff(pred_def_20, type, times_1: ('Integer_0()' * 'Integer_0()' * 'Integer_0()') > $o).
tff(pred_def_21, type, x_8: ('Integer_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_22, type, plus_1: ('Integer_0()' * 'Integer_0()' * 'Integer_0()') > $o).
tff(pred_def_23, type, sP0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_24, type, sP1: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_25, type, sP2: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_26, type, sP3: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_27, type, sP4: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_28, type, sP5: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_29, type, sP6: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_30, type, sP7: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_31, type, sP8: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_32, type, sP9: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_33, type, sP10: ('Integer_0()' * 'Integer_0()' * 'Integer_0()') > $o).
tff(pred_def_34, type, sP11: ('Integer_0()' * 'Integer_0()' * 'Integer_0()' * 'Integer_0()') > $o).
tff(pred_def_35, type, sP12: ('Integer_0()' * 'Integer_0()' * 'Integer_0()' * 'Integer_0()') > $o).
tff(pred_def_36, type, sP13: ('Nat_0()' * 'Integer_0()' * 'Nat_0()') > $o).
tff(pred_def_37, type, sP14: ('Sign_0()' * 'Integer_0()' * 'Sign_0()') > $o).
tff(pred_def_38, type, sP15: ('Integer_0()' * 'Integer_0()' * 'Nat_0()') > $o).
tff(pred_def_39, type, sP16: ('Sign_0()' * 'Integer_0()' * 'Integer_0()') > $o).
tff(f8689,plain,(
  $false),
  inference(subsumption_resolution,[],[f8687,f7830])).
tff(f7830,plain,(
  sP11('P_1'(zero_0),'P_1'(succ_0(zero_0)),'N_0'(zero_0),'N_0'(zero_0))),
  inference(unit_resulting_resolution,[],[f330,f7720,f199])).
tff(f199,plain,(
  ( ! [X6 : 'Integer_0()',X4 : 'Integer_0()',X0 : 'Integer_0()',X5 : 'Integer_0()',X3 : 'Integer_0()'] : (sP11(X5,X3,X0,X6) | ~plus_1(X3,X5,X4) | ~times_1(X4,X6,X0)) )),
  inference(cnf_transformation,[],[f199_D])).
tff(f199_D,plain,(
  ( ! [X6,X0,X3,X5] : (( ! [X4] : (~plus_1(X3,X5,X4) | ~times_1(X4,X6,X0)) ) <=> ~sP11(X5,X3,X0,X6)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP11])])).
tff(f7720,plain,(
  times_1('P_1'(succ_0(zero_0)),'N_0'(zero_0),'N_0'(zero_0))),
  inference(unit_resulting_resolution,[],[f145,f895,f569,f210])).
tff(f210,plain,(
  ( ! [X6 : 'Nat_0()',X2 : 'Integer_0()',X8 : 'Integer_0()',X7 : 'Integer_0()',X3 : 'Sign_0()'] : (~sP16(X3,X2,X7) | ~toInteger_0(X8,X3,X6) | ~sP15(X2,X7,X6) | times_1(X8,X7,X2)) )),
  inference(general_splitting,[],[f208,f209_D])).
tff(f209,plain,(
  ( ! [X2 : 'Integer_0()',X7 : 'Integer_0()',X3 : 'Sign_0()',X1 : 'Sign_0()'] : (~sP14(X3,X2,X1) | ~sign_1(X1,X7) | sP16(X3,X2,X7)) )),
  inference(cnf_transformation,[],[f209_D])).
tff(f209_D,plain,(
  ( ! [X7,X2,X3] : (( ! [X1] : (~sP14(X3,X2,X1) | ~sign_1(X1,X7)) ) <=> ~sP16(X3,X2,X7)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP16])])).
tff(f208,plain,(
  ( ! [X6 : 'Nat_0()',X2 : 'Integer_0()',X8 : 'Integer_0()',X7 : 'Integer_0()',X3 : 'Sign_0()',X1 : 'Sign_0()'] : (times_1(X8,X7,X2) | ~sign_1(X1,X7) | ~toInteger_0(X8,X3,X6) | ~sP14(X3,X2,X1) | ~sP15(X2,X7,X6)) )),
  inference(general_splitting,[],[f206,f207_D])).
tff(f207,plain,(
  ( ! [X6 : 'Nat_0()',X2 : 'Integer_0()',X7 : 'Integer_0()',X5 : 'Nat_0()'] : (~sP13(X6,X7,X5) | ~absVal_0(X5,X2) | sP15(X2,X7,X6)) )),
  inference(cnf_transformation,[],[f207_D])).
tff(f207_D,plain,(
  ( ! [X6,X7,X2] : (( ! [X5] : (~sP13(X6,X7,X5) | ~absVal_0(X5,X2)) ) <=> ~sP15(X2,X7,X6)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP15])])).
tff(f206,plain,(
  ( ! [X6 : 'Nat_0()',X2 : 'Integer_0()',X8 : 'Integer_0()',X7 : 'Integer_0()',X5 : 'Nat_0()',X3 : 'Sign_0()',X1 : 'Sign_0()'] : (times_1(X8,X7,X2) | ~sign_1(X1,X7) | ~absVal_0(X5,X2) | ~toInteger_0(X8,X3,X6) | ~sP13(X6,X7,X5) | ~sP14(X3,X2,X1)) )),
  inference(general_splitting,[],[f204,f205_D])).
tff(f205,plain,(
  ( ! [X2 : 'Integer_0()',X0 : 'Sign_0()',X3 : 'Sign_0()',X1 : 'Sign_0()'] : (~timesSign_0(X3,X1,X0) | ~sign_1(X0,X2) | sP14(X3,X2,X1)) )),
  inference(cnf_transformation,[],[f205_D])).
tff(f205_D,plain,(
  ( ! [X1,X2,X3] : (( ! [X0] : (~timesSign_0(X3,X1,X0) | ~sign_1(X0,X2)) ) <=> ~sP14(X3,X2,X1)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP14])])).
tff(f204,plain,(
  ( ! [X6 : 'Nat_0()',X2 : 'Integer_0()',X0 : 'Sign_0()',X8 : 'Integer_0()',X7 : 'Integer_0()',X5 : 'Nat_0()',X3 : 'Sign_0()',X1 : 'Sign_0()'] : (times_1(X8,X7,X2) | ~sign_1(X1,X7) | ~sign_1(X0,X2) | ~timesSign_0(X3,X1,X0) | ~absVal_0(X5,X2) | ~toInteger_0(X8,X3,X6) | ~sP13(X6,X7,X5)) )),
  inference(general_splitting,[],[f176,f203_D])).
tff(f203,plain,(
  ( ! [X6 : 'Nat_0()',X4 : 'Nat_0()',X7 : 'Integer_0()',X5 : 'Nat_0()'] : (~times_0(X6,X4,X5) | ~absVal_0(X4,X7) | sP13(X6,X7,X5)) )),
  inference(cnf_transformation,[],[f203_D])).
tff(f203_D,plain,(
  ( ! [X5,X7,X6] : (( ! [X4] : (~times_0(X6,X4,X5) | ~absVal_0(X4,X7)) ) <=> ~sP13(X6,X7,X5)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP13])])).
tff(f176,plain,(
  ( ! [X6 : 'Nat_0()',X4 : 'Nat_0()',X2 : 'Integer_0()',X0 : 'Sign_0()',X8 : 'Integer_0()',X7 : 'Integer_0()',X5 : 'Nat_0()',X3 : 'Sign_0()',X1 : 'Sign_0()'] : (times_1(X8,X7,X2) | ~sign_1(X1,X7) | ~sign_1(X0,X2) | ~timesSign_0(X3,X1,X0) | ~absVal_0(X4,X7) | ~absVal_0(X5,X2) | ~times_0(X6,X4,X5) | ~toInteger_0(X8,X3,X6)) )),
  inference(cnf_transformation,[],[f121])).
tff(f121,plain,(
  ! [X0 : 'Sign_0()',X1 : 'Sign_0()',X2 : 'Integer_0()',X3 : 'Sign_0()',X4 : 'Nat_0()',X5 : 'Nat_0()',X6 : 'Nat_0()',X7 : 'Integer_0()',X8 : 'Integer_0()'] : (times_1(X8,X7,X2) | ~sign_1(X1,X7) | ~sign_1(X0,X2) | ~timesSign_0(X3,X1,X0) | ~absVal_0(X4,X7) | ~absVal_0(X5,X2) | ~times_0(X6,X4,X5) | ~toInteger_0(X8,X3,X6))),
  inference(flattening,[],[f120])).
tff(f120,plain,(
  ! [X0 : 'Sign_0()',X1 : 'Sign_0()',X2 : 'Integer_0()',X3 : 'Sign_0()',X4 : 'Nat_0()',X5 : 'Nat_0()',X6 : 'Nat_0()',X7 : 'Integer_0()',X8 : 'Integer_0()'] : (times_1(X8,X7,X2) | (~sign_1(X1,X7) | ~sign_1(X0,X2) | ~timesSign_0(X3,X1,X0) | ~absVal_0(X4,X7) | ~absVal_0(X5,X2) | ~times_0(X6,X4,X5) | ~toInteger_0(X8,X3,X6)))),
  inference(ennf_transformation,[],[f90])).
tff(f90,plain,(
  ! [X0 : 'Sign_0()',X1 : 'Sign_0()',X2 : 'Integer_0()',X3 : 'Sign_0()',X4 : 'Nat_0()',X5 : 'Nat_0()',X6 : 'Nat_0()',X7 : 'Integer_0()',X8 : 'Integer_0()'] : ((sign_1(X1,X7) & sign_1(X0,X2) & timesSign_0(X3,X1,X0) & absVal_0(X4,X7) & absVal_0(X5,X2) & times_0(X6,X4,X5) & toInteger_0(X8,X3,X6)) => times_1(X8,X7,X2))),
  inference(rectify,[],[f34])).
tff(f34,axiom,(
  ! [X2 : 'Sign_0()',X1 : 'Sign_0()',X8 : 'Integer_0()',X3 : 'Sign_0()',X4 : 'Nat_0()',X5 : 'Nat_0()',X6 : 'Nat_0()',X7 : 'Integer_0()',X0 : 'Integer_0()'] : ((sign_1(X1,X7) & sign_1(X2,X8) & timesSign_0(X3,X1,X2) & absVal_0(X4,X7) & absVal_0(X5,X8) & times_0(X6,X4,X5) & toInteger_0(X0,X3,X6)) => times_1(X0,X7,X8))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f569,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (sP16('Pos_0','N_0'(X0),'N_0'(X1))) )),
  inference(unit_resulting_resolution,[],[f135,f547,f209])).
tff(f547,plain,(
  ( ! [X0 : 'Nat_0()'] : (sP14('Pos_0','N_0'(X0),'Neg_0')) )),
  inference(unit_resulting_resolution,[],[f135,f211,f205])).
tff(f211,plain,(
  timesSign_0('Pos_0','Neg_0','Neg_0')),
  inference(unit_resulting_resolution,[],[f127,f151])).
tff(f151,plain,(
  ( ! [X0 : 'Sign_0()',X1 : 'Sign_0()'] : (timesSign_0(X1,'Neg_0',X0) | ~opposite_0(X1,X0)) )),
  inference(cnf_transformation,[],[f91])).
tff(f91,plain,(
  ! [X0 : 'Sign_0()',X1 : 'Sign_0()'] : (timesSign_0(X1,'Neg_0',X0) | ~opposite_0(X1,X0))),
  inference(ennf_transformation,[],[f57])).
tff(f57,plain,(
  ! [X0 : 'Sign_0()',X1 : 'Sign_0()'] : (opposite_0(X1,X0) => timesSign_0(X1,'Neg_0',X0))),
  inference(rectify,[],[f30])).
tff(f30,axiom,(
  ! [X1 : 'Sign_0()',X0 : 'Sign_0()'] : (opposite_0(X0,X1) => timesSign_0(X0,'Neg_0',X1))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f127,plain,(
  opposite_0('Pos_0','Neg_0')),
  inference(cnf_transformation,[],[f28])).
tff(f28,axiom,(
  opposite_0('Pos_0','Neg_0')),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f135,plain,(
  ( ! [X0 : 'Nat_0()'] : (sign_1('Neg_0','N_0'(X0))) )),
  inference(cnf_transformation,[],[f22])).
tff(f22,axiom,(
  ! [X0 : 'Nat_0()'] : sign_1('Neg_0','N_0'(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f895,plain,(
  sP15('N_0'(zero_0),'N_0'(zero_0),succ_0(zero_0))),
  inference(unit_resulting_resolution,[],[f280,f845,f207])).
tff(f845,plain,(
  sP13(succ_0(zero_0),'N_0'(zero_0),succ_0(zero_0))),
  inference(unit_resulting_resolution,[],[f280,f770,f203])).
tff(f770,plain,(
  times_0(succ_0(zero_0),succ_0(zero_0),succ_0(zero_0))),
  inference(unit_resulting_resolution,[],[f269,f142,f166])).
tff(f166,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X3 : 'Nat_0()',X1 : 'Nat_0()'] : (~times_0(X2,X1,X0) | times_0(X3,succ_0(X1),X0) | ~plus_0(X3,X0,X2)) )),
  inference(cnf_transformation,[],[f107])).
tff(f107,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'Nat_0()'] : (times_0(X3,succ_0(X1),X0) | ~times_0(X2,X1,X0) | ~plus_0(X3,X0,X2))),
  inference(flattening,[],[f106])).
tff(f106,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'Nat_0()'] : (times_0(X3,succ_0(X1),X0) | (~times_0(X2,X1,X0) | ~plus_0(X3,X0,X2)))),
  inference(ennf_transformation,[],[f74])).
tff(f74,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'Nat_0()'] : ((times_0(X2,X1,X0) & plus_0(X3,X0,X2)) => times_0(X3,succ_0(X1),X0))),
  inference(rectify,[],[f26])).
tff(f26,axiom,(
  ! [X3 : 'Nat_0()',X2 : 'Nat_0()',X1 : 'Nat_0()',X0 : 'Nat_0()'] : ((times_0(X1,X2,X3) & plus_0(X0,X3,X1)) => times_0(X0,succ_0(X2),X3))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f142,plain,(
  ( ! [X0 : 'Nat_0()'] : (times_0(zero_0,zero_0,X0)) )),
  inference(cnf_transformation,[],[f27])).
tff(f27,axiom,(
  ! [X0 : 'Nat_0()'] : times_0(zero_0,zero_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f269,plain,(
  ( ! [X0 : 'Nat_0()'] : (plus_0(succ_0(X0),succ_0(zero_0),X0)) )),
  inference(unit_resulting_resolution,[],[f144,f162])).
tff(f162,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (plus_0(succ_0(X1),succ_0(X0),X2) | ~plus_0(X1,X0,X2)) )),
  inference(cnf_transformation,[],[f102])).
tff(f102,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (plus_0(succ_0(X1),succ_0(X0),X2) | ~plus_0(X1,X0,X2))),
  inference(ennf_transformation,[],[f69])).
tff(f69,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (plus_0(X1,X0,X2) => plus_0(succ_0(X1),succ_0(X0),X2))),
  inference(rectify,[],[f24])).
tff(f24,axiom,(
  ! [X1 : 'Nat_0()',X0 : 'Nat_0()',X2 : 'Nat_0()'] : (plus_0(X0,X1,X2) => plus_0(succ_0(X0),succ_0(X1),X2))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f144,plain,(
  ( ! [X0 : 'Nat_0()'] : (plus_0(X0,zero_0,X0)) )),
  inference(cnf_transformation,[],[f25])).
tff(f25,axiom,(
  ! [X0 : 'Nat_0()'] : plus_0(X0,zero_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f280,plain,(
  ( ! [X0 : 'Nat_0()'] : (absVal_0(succ_0(X0),'N_0'(X0))) )),
  inference(unit_resulting_resolution,[],[f269,f155])).
tff(f155,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (~plus_0(X0,succ_0(zero_0),X1) | absVal_0(X0,'N_0'(X1))) )),
  inference(cnf_transformation,[],[f95])).
tff(f95,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (absVal_0(X0,'N_0'(X1)) | ~plus_0(X0,succ_0(zero_0),X1))),
  inference(ennf_transformation,[],[f32])).
tff(f32,axiom,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (plus_0(X0,succ_0(zero_0),X1) => absVal_0(X0,'N_0'(X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f145,plain,(
  ( ! [X0 : 'Nat_0()'] : (toInteger_0('P_1'(X0),'Pos_0',X0)) )),
  inference(cnf_transformation,[],[f21])).
tff(f21,axiom,(
  ! [X0 : 'Nat_0()'] : toInteger_0('P_1'(X0),'Pos_0',X0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f330,plain,(
  ( ! [X0 : 'Nat_0()'] : (plus_1('P_1'(X0),'P_1'(zero_0),'P_1'(X0))) )),
  inference(unit_resulting_resolution,[],[f144,f163])).
tff(f163,plain,(
  ( ! [X2 : 'Nat_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (plus_1('P_1'(X1),'P_1'(X2),'P_1'(X0)) | ~plus_0(X1,X2,X0)) )),
  inference(cnf_transformation,[],[f103])).
tff(f103,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (plus_1('P_1'(X1),'P_1'(X2),'P_1'(X0)) | ~plus_0(X1,X2,X0))),
  inference(ennf_transformation,[],[f70])).
tff(f70,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Nat_0()'] : (plus_0(X1,X2,X0) => plus_1('P_1'(X1),'P_1'(X2),'P_1'(X0)))),
  inference(rectify,[],[f42])).
tff(f42,axiom,(
  ! [X1 : 'Nat_0()',X0 : 'Nat_0()',X2 : 'Nat_0()'] : (plus_0(X0,X2,X1) => plus_1('P_1'(X0),'P_1'(X2),'P_1'(X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f8687,plain,(
  ~sP11('P_1'(zero_0),'P_1'(succ_0(zero_0)),'N_0'(zero_0),'N_0'(zero_0))),
  inference(unit_resulting_resolution,[],[f8631,f7794,f202])).
tff(f202,plain,(
  ( ! [X6 : 'Integer_0()',X0 : 'Integer_0()',X5 : 'Integer_0()',X3 : 'Integer_0()',X1 : 'Integer_0()'] : (~sP12(X5,X1,X0,X6) | ~sP11(X5,X3,X0,X6) | ~sP10(X3,X1,X6)) )),
  inference(general_splitting,[],[f200,f201_D])).
tff(f201,plain,(
  ( ! [X6 : 'Integer_0()',X0 : 'Integer_0()',X7 : 'Integer_0()',X5 : 'Integer_0()',X1 : 'Integer_0()'] : (sP12(X5,X1,X0,X6) | ~times_1(X5,X6,X7) | ~plus_1(X1,X7,X0)) )),
  inference(cnf_transformation,[],[f201_D])).
tff(f201_D,plain,(
  ( ! [X6,X0,X1,X5] : (( ! [X7] : (~times_1(X5,X6,X7) | ~plus_1(X1,X7,X0)) ) <=> ~sP12(X5,X1,X0,X6)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP12])])).
tff(f200,plain,(
  ( ! [X6 : 'Integer_0()',X0 : 'Integer_0()',X7 : 'Integer_0()',X5 : 'Integer_0()',X3 : 'Integer_0()',X1 : 'Integer_0()'] : (~plus_1(X1,X7,X0) | ~times_1(X5,X6,X7) | ~sP10(X3,X1,X6) | ~sP11(X5,X3,X0,X6)) )),
  inference(general_splitting,[],[f198,f199_D])).
tff(f198,plain,(
  ( ! [X6 : 'Integer_0()',X4 : 'Integer_0()',X0 : 'Integer_0()',X7 : 'Integer_0()',X5 : 'Integer_0()',X3 : 'Integer_0()',X1 : 'Integer_0()'] : (~plus_1(X1,X7,X0) | ~times_1(X5,X6,X7) | ~times_1(X4,X6,X0) | ~plus_1(X3,X5,X4) | ~sP10(X3,X1,X6)) )),
  inference(general_splitting,[],[f175,f197_D])).
tff(f197,plain,(
  ( ! [X6 : 'Integer_0()',X2 : 'Integer_0()',X3 : 'Integer_0()',X1 : 'Integer_0()'] : (~times_1(X2,X6,X1) | ~diseqInteger_0(X2,X3) | sP10(X3,X1,X6)) )),
  inference(cnf_transformation,[],[f197_D])).
tff(f197_D,plain,(
  ( ! [X6,X1,X3] : (( ! [X2] : (~times_1(X2,X6,X1) | ~diseqInteger_0(X2,X3)) ) <=> ~sP10(X3,X1,X6)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).
tff(f175,plain,(
  ( ! [X6 : 'Integer_0()',X4 : 'Integer_0()',X2 : 'Integer_0()',X0 : 'Integer_0()',X7 : 'Integer_0()',X5 : 'Integer_0()',X3 : 'Integer_0()',X1 : 'Integer_0()'] : (~diseqInteger_0(X2,X3) | ~plus_1(X1,X7,X0) | ~times_1(X2,X6,X1) | ~times_1(X5,X6,X7) | ~times_1(X4,X6,X0) | ~plus_1(X3,X5,X4)) )),
  inference(cnf_transformation,[],[f119])).
tff(f119,plain,(
  ! [X0 : 'Integer_0()',X1 : 'Integer_0()',X2 : 'Integer_0()',X3 : 'Integer_0()',X4 : 'Integer_0()',X5 : 'Integer_0()',X6 : 'Integer_0()',X7 : 'Integer_0()'] : (~diseqInteger_0(X2,X3) | ~plus_1(X1,X7,X0) | ~times_1(X2,X6,X1) | ~times_1(X5,X6,X7) | ~times_1(X4,X6,X0) | ~plus_1(X3,X5,X4))),
  inference(ennf_transformation,[],[f89])).
tff(f89,plain,(
  ! [X0 : 'Integer_0()',X1 : 'Integer_0()',X2 : 'Integer_0()',X3 : 'Integer_0()',X4 : 'Integer_0()',X5 : 'Integer_0()',X6 : 'Integer_0()',X7 : 'Integer_0()'] : ~(diseqInteger_0(X2,X3) & plus_1(X1,X7,X0) & times_1(X2,X6,X1) & times_1(X5,X6,X7) & times_1(X4,X6,X0) & plus_1(X3,X5,X4))),
  inference(true_and_false_elimination,[],[f88])).
tff(f88,plain,(
  ! [X0 : 'Integer_0()',X1 : 'Integer_0()',X2 : 'Integer_0()',X3 : 'Integer_0()',X4 : 'Integer_0()',X5 : 'Integer_0()',X6 : 'Integer_0()',X7 : 'Integer_0()'] : ((diseqInteger_0(X2,X3) & plus_1(X1,X7,X0) & times_1(X2,X6,X1) & times_1(X5,X6,X7) & times_1(X4,X6,X0) & plus_1(X3,X5,X4)) => $false)),
  inference(rectify,[],[f43])).
tff(f43,axiom,(
  ! [X7 : 'Integer_0()',X0 : 'Integer_0()',X1 : 'Integer_0()',X4 : 'Integer_0()',X3 : 'Integer_0()',X2 : 'Integer_0()',X5 : 'Integer_0()',X6 : 'Integer_0()'] : ((diseqInteger_0(X1,X4) & plus_1(X0,X6,X7) & times_1(X1,X5,X0) & times_1(X2,X5,X6) & times_1(X3,X5,X7) & plus_1(X4,X2,X3)) => $false)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f7794,plain,(
  ( ! [X0 : 'Nat_0()'] : (sP12('P_1'(zero_0),'N_0'(succ_0(X0)),'N_0'(X0),'N_0'(zero_0))) )),
  inference(unit_resulting_resolution,[],[f6567,f7728,f201])).
tff(f7728,plain,(
  times_1('P_1'(zero_0),'N_0'(zero_0),'P_1'(zero_0))),
  inference(unit_resulting_resolution,[],[f129,f814,f570,f210])).
tff(f570,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (sP16('Neg_0','P_1'(X0),'N_0'(X1))) )),
  inference(unit_resulting_resolution,[],[f135,f548,f209])).
tff(f548,plain,(
  ( ! [X0 : 'Nat_0()'] : (sP14('Neg_0','P_1'(X0),'Neg_0')) )),
  inference(unit_resulting_resolution,[],[f134,f212,f205])).
tff(f212,plain,(
  timesSign_0('Neg_0','Neg_0','Pos_0')),
  inference(unit_resulting_resolution,[],[f128,f151])).
tff(f128,plain,(
  opposite_0('Neg_0','Pos_0')),
  inference(cnf_transformation,[],[f29])).
tff(f29,axiom,(
  opposite_0('Neg_0','Pos_0')),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f134,plain,(
  ( ! [X0 : 'Nat_0()'] : (sign_1('Pos_0','P_1'(X0))) )),
  inference(cnf_transformation,[],[f23])).
tff(f23,axiom,(
  ! [X0 : 'Nat_0()'] : sign_1('Pos_0','P_1'(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f814,plain,(
  sP15('P_1'(zero_0),'N_0'(zero_0),zero_0)),
  inference(unit_resulting_resolution,[],[f141,f798,f207])).
tff(f798,plain,(
  sP13(zero_0,'N_0'(zero_0),zero_0)),
  inference(unit_resulting_resolution,[],[f280,f769,f203])).
tff(f769,plain,(
  times_0(zero_0,succ_0(zero_0),zero_0)),
  inference(unit_resulting_resolution,[],[f144,f142,f166])).
tff(f141,plain,(
  ( ! [X0 : 'Nat_0()'] : (absVal_0(X0,'P_1'(X0))) )),
  inference(cnf_transformation,[],[f33])).
tff(f33,axiom,(
  ! [X0 : 'Nat_0()'] : absVal_0(X0,'P_1'(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f129,plain,(
  toInteger_0('P_1'(zero_0),'Neg_0',zero_0)),
  inference(cnf_transformation,[],[f20])).
tff(f20,axiom,(
  toInteger_0('P_1'(zero_0),'Neg_0',zero_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f6567,plain,(
  ( ! [X0 : 'Nat_0()'] : (plus_1('N_0'(succ_0(X0)),'P_1'(zero_0),'N_0'(X0))) )),
  inference(unit_resulting_resolution,[],[f147,f269,f170])).
tff(f170,plain,(
  ( ! [X2 : 'Integer_0()',X0 : 'Nat_0()',X3 : 'Nat_0()',X1 : 'Nat_0()'] : (plus_1(X2,'P_1'(X1),'N_0'(X3)) | ~plus_0(X0,succ_0(zero_0),X3) | ~x_8(X2,X1,X0)) )),
  inference(cnf_transformation,[],[f114])).
tff(f114,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Integer_0()',X3 : 'Nat_0()'] : (plus_1(X2,'P_1'(X1),'N_0'(X3)) | ~plus_0(X0,succ_0(zero_0),X3) | ~x_8(X2,X1,X0))),
  inference(flattening,[],[f113])).
tff(f113,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Integer_0()',X3 : 'Nat_0()'] : (plus_1(X2,'P_1'(X1),'N_0'(X3)) | (~plus_0(X0,succ_0(zero_0),X3) | ~x_8(X2,X1,X0)))),
  inference(ennf_transformation,[],[f79])).
tff(f79,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'Integer_0()',X3 : 'Nat_0()'] : ((plus_0(X0,succ_0(zero_0),X3) & x_8(X2,X1,X0)) => plus_1(X2,'P_1'(X1),'N_0'(X3)))),
  inference(rectify,[],[f41])).
tff(f41,axiom,(
  ! [X1 : 'Nat_0()',X3 : 'Nat_0()',X0 : 'Integer_0()',X2 : 'Nat_0()'] : ((plus_0(X1,succ_0(zero_0),X2) & x_8(X0,X3,X1)) => plus_1(X0,'P_1'(X3),'N_0'(X2)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f147,plain,(
  ( ! [X0 : 'Nat_0()'] : (x_8('N_0'(succ_0(X0)),zero_0,succ_0(X0))) )),
  inference(cnf_transformation,[],[f36])).
tff(f36,axiom,(
  ! [X0 : 'Nat_0()'] : x_8('N_0'(succ_0(X0)),zero_0,succ_0(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f8631,plain,(
  sP10('P_1'(succ_0(zero_0)),'N_0'(succ_0(zero_0)),'N_0'(zero_0))),
  inference(unit_resulting_resolution,[],[f244,f7721,f197])).
tff(f7721,plain,(
  times_1('P_1'(succ_0(succ_0(zero_0))),'N_0'(zero_0),'N_0'(succ_0(zero_0)))),
  inference(unit_resulting_resolution,[],[f145,f1046,f569,f210])).
tff(f1046,plain,(
  sP15('N_0'(succ_0(zero_0)),'N_0'(zero_0),succ_0(succ_0(zero_0)))),
  inference(unit_resulting_resolution,[],[f280,f991,f207])).
tff(f991,plain,(
  sP13(succ_0(succ_0(zero_0)),'N_0'(zero_0),succ_0(succ_0(zero_0)))),
  inference(unit_resulting_resolution,[],[f280,f771,f203])).
tff(f771,plain,(
  times_0(succ_0(succ_0(zero_0)),succ_0(zero_0),succ_0(succ_0(zero_0)))),
  inference(unit_resulting_resolution,[],[f282,f142,f166])).
tff(f282,plain,(
  ( ! [X0 : 'Nat_0()'] : (plus_0(succ_0(succ_0(X0)),succ_0(succ_0(zero_0)),X0)) )),
  inference(unit_resulting_resolution,[],[f269,f162])).
tff(f244,plain,(
  ( ! [X0 : 'Nat_0()'] : (diseqInteger_0('P_1'(succ_0(succ_0(X0))),'P_1'(succ_0(zero_0)))) )),
  inference(unit_resulting_resolution,[],[f228,f154])).
tff(f154,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (diseqInteger_0('P_1'(X0),'P_1'(X1)) | ~diseqNat_0(X0,X1)) )),
  inference(cnf_transformation,[],[f94])).
tff(f94,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (diseqInteger_0('P_1'(X0),'P_1'(X1)) | ~diseqNat_0(X0,X1))),
  inference(ennf_transformation,[],[f17])).
tff(f17,axiom,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (diseqNat_0(X0,X1) => diseqInteger_0('P_1'(X0),'P_1'(X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f228,plain,(
  ( ! [X0 : 'Nat_0()'] : (diseqNat_0(succ_0(succ_0(X0)),succ_0(zero_0))) )),
  inference(unit_resulting_resolution,[],[f137,f152])).
tff(f152,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (diseqNat_0(succ_0(X1),succ_0(X0)) | ~diseqNat_0(X1,X0)) )),
  inference(cnf_transformation,[],[f92])).
tff(f92,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (diseqNat_0(succ_0(X1),succ_0(X0)) | ~diseqNat_0(X1,X0))),
  inference(ennf_transformation,[],[f58])).
tff(f58,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()'] : (diseqNat_0(X1,X0) => diseqNat_0(succ_0(X1),succ_0(X0)))),
  inference(rectify,[],[f10])).
tff(f10,axiom,(
  ! [X1 : 'Nat_0()',X0 : 'Nat_0()'] : (diseqNat_0(X0,X1) => diseqNat_0(succ_0(X0),succ_0(X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
tff(f137,plain,(
  ( ! [X0 : 'Nat_0()'] : (diseqNat_0(succ_0(X0),zero_0)) )),
  inference(cnf_transformation,[],[f9])).
tff(f9,axiom,(
  ! [X0 : 'Nat_0()'] : diseqNat_0(succ_0(X0),zero_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/tests/generated/OriginalSolve/TIP.FreeSorts/tip2015/int_left_distrib.smt2',unknown)).
