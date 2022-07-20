3
12900
30
UNSAT
% lrs+2_1_lcm=predicate_20 on tmpJBlq8L.
tff(type_def_5, type, 'adtConstr_0()': $tType).
tff(type_def_6, type, 'State_0()': $tType).
tff(func_def_0, type, adtConstrbot_0: 'adtConstr_0()').
tff(func_def_1, type, initeven_0: 'State_0()').
tff(func_def_2, type, deltaeven_0: ('adtConstr_0()' * 'State_0()') > 'State_0()').
tff(func_def_3, type, initpat_0: 'State_0()').
tff(func_def_4, type, deltapat_0: ('State_0()') > 'State_0()').
tff(func_def_5, type, initpat_1: 'State_0()').
tff(func_def_6, type, deltapat_1: ('adtConstr_0()' * 'State_0()') > 'State_0()').
tff(func_def_7, type, initpat_2: 'State_0()').
tff(func_def_8, type, deltapat_2: ('adtConstr_0()' * 'State_0()') > 'State_0()').
tff(func_def_9, type, prod_0: ('State_0()' * 'State_0()') > 'State_0()').
tff(func_def_10, type, 'Z_0': 'adtConstr_0()').
tff(func_def_11, type, 'S_0': 'adtConstr_0()').
tff(func_def_12, type, initclause_0: 'State_0()').
tff(func_def_13, type, deltaclause_0: ('State_0()') > 'State_0()').
tff(func_def_14, type, initclause_1: 'State_0()').
tff(func_def_15, type, deltaclause_1: ('adtConstr_0()' * 'State_0()') > 'State_0()').
tff(func_def_16, type, initclause_2: 'State_0()').
tff(func_def_17, type, deltaclause_2: ('adtConstr_0()' * 'State_0()') > 'State_0()').
tff(pred_def_1, type, isFinaleven_0: ('State_0()') > $o).
tff(pred_def_2, type, reacheven_0: ('State_0()') > $o).
tff(pred_def_3, type, isFinalpat_0: ('State_0()') > $o).
tff(pred_def_4, type, reachpat_0: ('State_0()') > $o).
tff(pred_def_5, type, isFinalpat_1: ('State_0()') > $o).
tff(pred_def_6, type, reachpat_1: ('State_0()') > $o).
tff(pred_def_7, type, isFinalpat_2: ('State_0()') > $o).
tff(pred_def_8, type, reachpat_2: ('State_0()') > $o).
tff(pred_def_9, type, isFinalclause_0: ('State_0()') > $o).
tff(pred_def_10, type, reachclause_0: ('State_0()') > $o).
tff(pred_def_11, type, isFinalclause_1: ('State_0()') > $o).
tff(pred_def_12, type, reachclause_1: ('State_0()') > $o).
tff(pred_def_13, type, isFinalclause_2: ('State_0()') > $o).
tff(pred_def_14, type, reachclause_2: ('State_0()') > $o).
tff(f280,plain,(
  $false),
  inference(avatar_sat_refutation,[],[f117,f129,f139,f141,f279])).
tff(f279,plain,(
  ~spl0_2),
  inference(avatar_contradiction_clause,[],[f277])).
tff(f277,plain,(
  $false | ~spl0_2),
  inference(resolution,[],[f273,f142])).
tff(f142,plain,(
  isFinaleven_0(deltapat_1('Z_0',initpat_1)) | ~spl0_2),
  inference(forward_demodulation,[],[f110,f96])).
tff(f96,plain,(
  ( ! [X0 : 'adtConstr_0()',X1 : 'State_0()'] : (deltapat_1(X0,X1) = deltapat_2(X0,X1)) )),
  inference(definition_unfolding,[],[f76,f75])).
tff(f75,plain,(
  ( ! [X0 : 'adtConstr_0()',X1 : 'State_0()'] : (deltaeven_0(X0,X1) = deltapat_2(X0,X1)) )),
  inference(cnf_transformation,[],[f11])).
tff(f11,axiom,(
  ! [X0 : 'adtConstr_0()',X1 : 'State_0()'] : deltaeven_0(X0,X1) = deltapat_2(X0,X1)),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f76,plain,(
  ( ! [X0 : 'adtConstr_0()',X1 : 'State_0()'] : (deltaeven_0(X0,X1) = deltapat_1(X0,X1)) )),
  inference(cnf_transformation,[],[f7])).
tff(f7,axiom,(
  ! [X0 : 'adtConstr_0()',X1 : 'State_0()'] : deltaeven_0(X0,X1) = deltapat_1(X0,X1)),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f110,plain,(
  isFinaleven_0(deltapat_2('Z_0',initpat_1)) | ~spl0_2),
  inference(avatar_component_clause,[],[f109])).
tff(f109,plain,(
  spl0_2 <=> isFinaleven_0(deltapat_2('Z_0',initpat_1))),
  introduced(avatar_definition,[new_symbols(naming,[spl0_2])])).
tff(f273,plain,(
  ( ! [X0 : 'adtConstr_0()'] : (~isFinaleven_0(deltapat_1(X0,initpat_1))) )),
  inference(resolution,[],[f266,f69])).
tff(f69,plain,(
  ( ! [X0 : 'State_0()'] : (isFinalpat_2(X0) | ~isFinaleven_0(X0)) )),
  inference(cnf_transformation,[],[f44])).
tff(f44,plain,(
  ! [X0 : 'State_0()'] : ((isFinalpat_2(X0) | ~isFinaleven_0(X0)) & (isFinaleven_0(X0) | ~isFinalpat_2(X0)))),
  inference(nnf_transformation,[],[f12])).
tff(f12,axiom,(
  ! [X0 : 'State_0()'] : (isFinalpat_2(X0) <=> isFinaleven_0(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f266,plain,(
  ( ! [X2 : 'adtConstr_0()'] : (~isFinalpat_2(deltapat_1(X2,initpat_1))) )),
  inference(subsumption_resolution,[],[f264,f53])).
tff(f53,plain,(
  reachclause_1(initclause_1)),
  inference(cnf_transformation,[],[f21])).
tff(f21,axiom,(
  reachclause_1(initclause_1)),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f264,plain,(
  ( ! [X2 : 'adtConstr_0()'] : (~isFinalpat_2(deltapat_1(X2,initpat_1)) | ~reachclause_1(initclause_1)) )),
  inference(resolution,[],[f259,f146])).
tff(f146,plain,(
  ( ! [X0 : 'State_0()',X1 : 'adtConstr_0()'] : (~isFinalclause_1(deltaclause_1(X1,X0)) | ~reachclause_1(X0)) )),
  inference(resolution,[],[f78,f72])).
tff(f72,plain,(
  ( ! [X0 : 'State_0()'] : (~reachclause_1(X0) | ~isFinalclause_1(X0)) )),
  inference(cnf_transformation,[],[f38])).
tff(f38,plain,(
  ! [X0 : 'State_0()'] : (~reachclause_1(X0) | ~isFinalclause_1(X0))),
  inference(ennf_transformation,[],[f23])).
tff(f23,axiom,(
  ! [X0 : 'State_0()'] : ~(reachclause_1(X0) & isFinalclause_1(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f78,plain,(
  ( ! [X0 : 'adtConstr_0()',X1 : 'State_0()'] : (reachclause_1(deltaclause_1(X0,X1)) | ~reachclause_1(X1)) )),
  inference(cnf_transformation,[],[f42])).
tff(f42,plain,(
  ! [X0 : 'adtConstr_0()',X1 : 'State_0()'] : (reachclause_1(deltaclause_1(X0,X1)) | ~reachclause_1(X1))),
  inference(ennf_transformation,[],[f22])).
tff(f22,axiom,(
  ! [X0 : 'adtConstr_0()',X1 : 'State_0()'] : (reachclause_1(X1) => reachclause_1(deltaclause_1(X0,X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f259,plain,(
  ( ! [X0 : 'adtConstr_0()'] : (isFinalclause_1(deltaclause_1(X0,initclause_1)) | ~isFinalpat_2(deltapat_1(X0,initpat_1))) )),
  inference(subsumption_resolution,[],[f255,f247])).
tff(f247,plain,(
  ( ! [X0 : 'adtConstr_0()'] : (~isFinalpat_2(deltapat_1(X0,initpat_1)) | ~isFinalpat_1(deltapat_1(X0,initpat_1))) )),
  inference(subsumption_resolution,[],[f243,f192])).
tff(f192,plain,(
  ( ! [X0 : 'adtConstr_0()'] : (~isFinalclause_2(deltaclause_1(X0,initclause_1))) )),
  inference(subsumption_resolution,[],[f190,f103])).
tff(f103,plain,(
  reachclause_2(initclause_1)),
  inference(backward_demodulation,[],[f52,f101])).
tff(f101,plain,(
  initclause_1 = initclause_2),
  inference(backward_demodulation,[],[f99,f100])).
tff(f100,plain,(
  initclause_1 = prod_0(initpat_1,initpat_1)),
  inference(forward_demodulation,[],[f63,f90])).
tff(f90,plain,(
  initpat_1 = initpat_2),
  inference(definition_unfolding,[],[f56,f55])).
tff(f55,plain,(
  initeven_0 = initpat_2),
  inference(cnf_transformation,[],[f10])).
tff(f10,axiom,(
  initeven_0 = initpat_2),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f56,plain,(
  initeven_0 = initpat_1),
  inference(cnf_transformation,[],[f6])).
tff(f6,axiom,(
  initeven_0 = initpat_1),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f63,plain,(
  prod_0(initpat_1,initpat_2) = initclause_1),
  inference(cnf_transformation,[],[f17])).
tff(f17,axiom,(
  prod_0(initpat_1,initpat_2) = initclause_1),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f99,plain,(
  initclause_2 = prod_0(initpat_1,initpat_1)),
  inference(forward_demodulation,[],[f62,f90])).
tff(f62,plain,(
  prod_0(initpat_2,initpat_1) = initclause_2),
  inference(cnf_transformation,[],[f24])).
tff(f24,axiom,(
  prod_0(initpat_2,initpat_1) = initclause_2),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f52,plain,(
  reachclause_2(initclause_2)),
  inference(cnf_transformation,[],[f28])).
tff(f28,axiom,(
  reachclause_2(initclause_2)),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f190,plain,(
  ( ! [X0 : 'adtConstr_0()'] : (~isFinalclause_2(deltaclause_1(X0,initclause_1)) | ~reachclause_2(initclause_1)) )),
  inference(superposition,[],[f144,f176])).
tff(f176,plain,(
  ( ! [X0 : 'adtConstr_0()'] : (deltaclause_2(X0,initclause_1) = deltaclause_1(X0,initclause_1)) )),
  inference(superposition,[],[f132,f100])).
tff(f132,plain,(
  ( ! [X2 : 'State_0()',X0 : 'State_0()',X1 : 'adtConstr_0()'] : (deltaclause_2(X1,prod_0(X2,X0)) = deltaclause_1(X1,prod_0(X2,X0))) )),
  inference(backward_demodulation,[],[f130,f131])).
tff(f131,plain,(
  ( ! [X2 : 'State_0()',X0 : 'adtConstr_0()',X1 : 'State_0()'] : (deltaclause_1(X0,prod_0(X2,X1)) = prod_0(deltapat_1(X0,X2),deltapat_1(X0,X1))) )),
  inference(forward_demodulation,[],[f88,f96])).
tff(f88,plain,(
  ( ! [X2 : 'State_0()',X0 : 'adtConstr_0()',X1 : 'State_0()'] : (prod_0(deltapat_1(X0,X2),deltapat_2(X0,X1)) = deltaclause_1(X0,prod_0(X2,X1))) )),
  inference(cnf_transformation,[],[f36])).
tff(f36,plain,(
  ! [X0 : 'adtConstr_0()',X1 : 'State_0()',X2 : 'State_0()'] : prod_0(deltapat_1(X0,X2),deltapat_2(X0,X1)) = deltaclause_1(X0,prod_0(X2,X1))),
  inference(rectify,[],[f19])).
tff(f19,axiom,(
  ! [X0 : 'adtConstr_0()',X2 : 'State_0()',X1 : 'State_0()'] : prod_0(deltapat_1(X0,X1),deltapat_2(X0,X2)) = deltaclause_1(X0,prod_0(X1,X2))),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f130,plain,(
  ( ! [X2 : 'State_0()',X0 : 'State_0()',X1 : 'adtConstr_0()'] : (deltaclause_2(X1,prod_0(X2,X0)) = prod_0(deltapat_1(X1,X2),deltapat_1(X1,X0))) )),
  inference(forward_demodulation,[],[f87,f96])).
tff(f87,plain,(
  ( ! [X2 : 'State_0()',X0 : 'State_0()',X1 : 'adtConstr_0()'] : (prod_0(deltapat_2(X1,X2),deltapat_1(X1,X0)) = deltaclause_2(X1,prod_0(X2,X0))) )),
  inference(cnf_transformation,[],[f35])).
tff(f35,plain,(
  ! [X0 : 'State_0()',X1 : 'adtConstr_0()',X2 : 'State_0()'] : prod_0(deltapat_2(X1,X2),deltapat_1(X1,X0)) = deltaclause_2(X1,prod_0(X2,X0))),
  inference(rectify,[],[f26])).
tff(f26,axiom,(
  ! [X2 : 'State_0()',X0 : 'adtConstr_0()',X1 : 'State_0()'] : prod_0(deltapat_2(X0,X1),deltapat_1(X0,X2)) = deltaclause_2(X0,prod_0(X1,X2))),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f144,plain,(
  ( ! [X0 : 'State_0()',X1 : 'adtConstr_0()'] : (~isFinalclause_2(deltaclause_2(X1,X0)) | ~reachclause_2(X0)) )),
  inference(resolution,[],[f77,f73])).
tff(f73,plain,(
  ( ! [X0 : 'State_0()'] : (~reachclause_2(X0) | ~isFinalclause_2(X0)) )),
  inference(cnf_transformation,[],[f39])).
tff(f39,plain,(
  ! [X0 : 'State_0()'] : (~reachclause_2(X0) | ~isFinalclause_2(X0))),
  inference(ennf_transformation,[],[f30])).
tff(f30,axiom,(
  ! [X0 : 'State_0()'] : ~(reachclause_2(X0) & isFinalclause_2(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f77,plain,(
  ( ! [X0 : 'adtConstr_0()',X1 : 'State_0()'] : (reachclause_2(deltaclause_2(X0,X1)) | ~reachclause_2(X1)) )),
  inference(cnf_transformation,[],[f41])).
tff(f41,plain,(
  ! [X0 : 'adtConstr_0()',X1 : 'State_0()'] : (reachclause_2(deltaclause_2(X0,X1)) | ~reachclause_2(X1))),
  inference(ennf_transformation,[],[f29])).
tff(f29,axiom,(
  ! [X0 : 'adtConstr_0()',X1 : 'State_0()'] : (reachclause_2(X1) => reachclause_2(deltaclause_2(X0,X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f243,plain,(
  ( ! [X0 : 'adtConstr_0()'] : (isFinalclause_2(deltaclause_1(X0,initclause_1)) | ~isFinalpat_2(deltapat_1(X0,initpat_1)) | ~isFinalpat_1(deltapat_1(X0,initpat_1))) )),
  inference(superposition,[],[f181,f100])).
tff(f181,plain,(
  ( ! [X2 : 'State_0()',X0 : 'adtConstr_0()',X1 : 'State_0()'] : (isFinalclause_2(deltaclause_1(X0,prod_0(X1,X2))) | ~isFinalpat_2(deltapat_1(X0,X1)) | ~isFinalpat_1(deltapat_1(X0,X2))) )),
  inference(superposition,[],[f79,f131])).
tff(f79,plain,(
  ( ! [X0 : 'State_0()',X1 : 'State_0()'] : (isFinalclause_2(prod_0(X0,X1)) | ~isFinalpat_2(X0) | ~isFinalpat_1(X1)) )),
  inference(cnf_transformation,[],[f47])).
tff(f47,plain,(
  ! [X0 : 'State_0()',X1 : 'State_0()'] : (((isFinalpat_2(X0) & isFinalpat_1(X1)) | ~isFinalclause_2(prod_0(X0,X1))) & (isFinalclause_2(prod_0(X0,X1)) | ~isFinalpat_2(X0) | ~isFinalpat_1(X1)))),
  inference(flattening,[],[f46])).
tff(f46,plain,(
  ! [X0 : 'State_0()',X1 : 'State_0()'] : (((isFinalpat_2(X0) & isFinalpat_1(X1)) | ~isFinalclause_2(prod_0(X0,X1))) & (isFinalclause_2(prod_0(X0,X1)) | (~isFinalpat_2(X0) | ~isFinalpat_1(X1))))),
  inference(nnf_transformation,[],[f27])).
tff(f27,axiom,(
  ! [X0 : 'State_0()',X1 : 'State_0()'] : ((isFinalpat_2(X0) & isFinalpat_1(X1)) <=> isFinalclause_2(prod_0(X0,X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f255,plain,(
  ( ! [X0 : 'adtConstr_0()'] : (isFinalclause_1(deltaclause_1(X0,initclause_1)) | isFinalpat_1(deltapat_1(X0,initpat_1)) | ~isFinalpat_2(deltapat_1(X0,initpat_1))) )),
  inference(superposition,[],[f184,f100])).
tff(f184,plain,(
  ( ! [X10 : 'State_0()',X11 : 'State_0()',X9 : 'adtConstr_0()'] : (isFinalclause_1(deltaclause_1(X9,prod_0(X10,X11))) | isFinalpat_1(deltapat_1(X9,X10)) | ~isFinalpat_2(deltapat_1(X9,X11))) )),
  inference(superposition,[],[f82,f131])).
tff(f82,plain,(
  ( ! [X0 : 'State_0()',X1 : 'State_0()'] : (isFinalclause_1(prod_0(X1,X0)) | isFinalpat_1(X1) | ~isFinalpat_2(X0)) )),
  inference(cnf_transformation,[],[f49])).
tff(f49,plain,(
  ! [X0 : 'State_0()',X1 : 'State_0()'] : (((~isFinalpat_1(X1) & isFinalpat_2(X0)) | ~isFinalclause_1(prod_0(X1,X0))) & (isFinalclause_1(prod_0(X1,X0)) | isFinalpat_1(X1) | ~isFinalpat_2(X0)))),
  inference(flattening,[],[f48])).
tff(f48,plain,(
  ! [X0 : 'State_0()',X1 : 'State_0()'] : (((~isFinalpat_1(X1) & isFinalpat_2(X0)) | ~isFinalclause_1(prod_0(X1,X0))) & (isFinalclause_1(prod_0(X1,X0)) | (isFinalpat_1(X1) | ~isFinalpat_2(X0))))),
  inference(nnf_transformation,[],[f32])).
tff(f32,plain,(
  ! [X0 : 'State_0()',X1 : 'State_0()'] : ((~isFinalpat_1(X1) & isFinalpat_2(X0)) <=> isFinalclause_1(prod_0(X1,X0)))),
  inference(flattening,[],[f31])).
tff(f31,plain,(
  ! [X0 : 'State_0()',X1 : 'State_0()'] : ((~isFinalpat_1(X1) & isFinalpat_2(X0)) <=> isFinalclause_1(prod_0(X1,X0)))),
  inference(rectify,[],[f20])).
tff(f20,axiom,(
  ! [X1 : 'State_0()',X0 : 'State_0()'] : ((~isFinalpat_1(X0) & isFinalpat_2(X1)) <=> isFinalclause_1(prod_0(X0,X1)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f141,plain,(
  ~spl0_1 | ~spl0_3),
  inference(avatar_contradiction_clause,[],[f140])).
tff(f140,plain,(
  $false | (~spl0_1 | ~spl0_3)),
  inference(subsumption_resolution,[],[f107,f116])).
tff(f116,plain,(
  ( ! [X0 : 'State_0()'] : (~isFinalpat_0(X0)) ) | ~spl0_3),
  inference(avatar_component_clause,[],[f115])).
tff(f115,plain,(
  spl0_3 <=> ! [X0 : 'State_0()'] : ~isFinalpat_0(X0)),
  introduced(avatar_definition,[new_symbols(naming,[spl0_3])])).
tff(f107,plain,(
  ( ! [X0 : 'State_0()'] : (isFinalpat_0(X0)) ) | ~spl0_1),
  inference(avatar_component_clause,[],[f106])).
tff(f106,plain,(
  spl0_1 <=> ! [X0 : 'State_0()'] : isFinalpat_0(X0)),
  introduced(avatar_definition,[new_symbols(naming,[spl0_1])])).
tff(f139,plain,(
  ~spl0_5),
  inference(avatar_contradiction_clause,[],[f138])).
tff(f138,plain,(
  $false | ~spl0_5),
  inference(subsumption_resolution,[],[f137,f128])).
tff(f128,plain,(
  ( ! [X1 : 'State_0()'] : (isFinalclause_0(X1)) ) | ~spl0_5),
  inference(avatar_component_clause,[],[f127])).
tff(f127,plain,(
  spl0_5 <=> ! [X1 : 'State_0()'] : isFinalclause_0(X1)),
  introduced(avatar_definition,[new_symbols(naming,[spl0_5])])).
tff(f137,plain,(
  ~isFinalclause_0(initclause_0)),
  inference(resolution,[],[f74,f51])).
tff(f51,plain,(
  reachclause_0(initclause_0)),
  inference(cnf_transformation,[],[f14])).
tff(f14,axiom,(
  reachclause_0(initclause_0)),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f74,plain,(
  ( ! [X0 : 'State_0()'] : (~reachclause_0(X0) | ~isFinalclause_0(X0)) )),
  inference(cnf_transformation,[],[f40])).
tff(f40,plain,(
  ! [X0 : 'State_0()'] : (~reachclause_0(X0) | ~isFinalclause_0(X0))),
  inference(ennf_transformation,[],[f16])).
tff(f16,axiom,(
  ! [X0 : 'State_0()'] : ~(reachclause_0(X0) & isFinalclause_0(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f129,plain,(
  spl0_1 | spl0_5),
  inference(avatar_split_clause,[],[f85,f127,f106])).
tff(f85,plain,(
  ( ! [X0 : 'State_0()',X1 : 'State_0()'] : (isFinalclause_0(X1) | isFinalpat_0(X0)) )),
  inference(cnf_transformation,[],[f50])).
tff(f50,plain,(
  ! [X0 : 'State_0()',X1 : 'State_0()'] : ((~isFinalpat_0(X0) | ~isFinalclause_0(X1)) & (isFinalclause_0(X1) | isFinalpat_0(X0)))),
  inference(nnf_transformation,[],[f34])).
tff(f34,plain,(
  ! [X0 : 'State_0()',X1 : 'State_0()'] : (~isFinalpat_0(X0) <=> isFinalclause_0(X1))),
  inference(flattening,[],[f33])).
tff(f33,plain,(
  ! [X0 : 'State_0()',X1 : 'State_0()'] : (~isFinalpat_0(X0) <=> isFinalclause_0(X1))),
  inference(rectify,[],[f13])).
tff(f13,axiom,(
  ! [X1 : 'State_0()',X0 : 'State_0()'] : (~isFinalpat_0(X1) <=> isFinalclause_0(X0))),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
tff(f117,plain,(
  spl0_3 | spl0_2),
  inference(avatar_split_clause,[],[f113,f109,f115])).
tff(f113,plain,(
  ( ! [X0 : 'State_0()'] : (isFinaleven_0(deltapat_2('Z_0',initpat_1)) | ~isFinalpat_0(X0)) )),
  inference(forward_demodulation,[],[f93,f90])).
tff(f93,plain,(
  ( ! [X0 : 'State_0()'] : (isFinaleven_0(deltapat_2('Z_0',initpat_2)) | ~isFinalpat_0(X0)) )),
  inference(definition_unfolding,[],[f66,f75,f55])).
tff(f66,plain,(
  ( ! [X0 : 'State_0()'] : (isFinaleven_0(deltaeven_0('Z_0',initeven_0)) | ~isFinalpat_0(X0)) )),
  inference(cnf_transformation,[],[f43])).
tff(f43,plain,(
  ! [X0 : 'State_0()'] : ((isFinalpat_0(X0) | ~isFinaleven_0(deltaeven_0('Z_0',initeven_0))) & (isFinaleven_0(deltaeven_0('Z_0',initeven_0)) | ~isFinalpat_0(X0)))),
  inference(nnf_transformation,[],[f4])).
tff(f4,axiom,(
  ! [X0 : 'State_0()'] : (isFinalpat_0(X0) <=> isFinaleven_0(deltaeven_0('Z_0',initeven_0)))),
  file('/home/columpio/RiderProjects/RInGen/Tests/samples/even.unsat.tta_unsat.generated/tmpJBlq8L..smt2',unknown)).
