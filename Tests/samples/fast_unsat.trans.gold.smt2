6
13224
80
UNSAT
% dis+10_10_lcm=reverse_20 on fast_unsat.FreeSorts
tff(type_def_5, type, 'Nat_0()': $tType).
tff(type_def_6, type, 'list_0()': $tType).
tff(type_def_7, type, 'E_0()': $tType).
tff(type_def_8, type, 'P_0()': $tType).
tff(type_def_9, type, 'list_1()': $tType).
tff(func_def_0, type, 'Z_0': 'Nat_0()').
tff(func_def_1, type, 'S_0': ('Nat_0()') > 'Nat_0()').
tff(func_def_2, type, nil_0: 'list_0()').
tff(func_def_3, type, cons_0: ('Nat_0()' * 'list_0()') > 'list_0()').
tff(func_def_4, type, 'N_0': ('Nat_0()') > 'E_0()').
tff(func_def_5, type, 'Add_0': ('E_0()' * 'E_0()') > 'E_0()').
tff(func_def_6, type, 'Mul_0': ('E_0()' * 'E_0()') > 'E_0()').
tff(func_def_7, type, 'Eq_0': ('E_0()' * 'E_0()') > 'E_0()').
tff(func_def_8, type, 'V_0': ('Nat_0()') > 'E_0()').
tff(func_def_9, type, 'Print_0': ('E_0()') > 'P_0()').
tff(func_def_10, type, x_0: ('Nat_0()' * 'E_0()') > 'P_0()').
tff(func_def_11, type, 'While_0': ('E_0()' * 'list_1()') > 'P_0()').
tff(func_def_12, type, 'If_0': ('E_0()' * 'list_1()' * 'list_1()') > 'P_0()').
tff(func_def_13, type, nil_1: 'list_1()').
tff(func_def_14, type, cons_1: ('P_0()' * 'list_1()') > 'list_1()').
tff(pred_def_1, type, diseqNat_0: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_2, type, add_1: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_3, type, minus_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_4, type, mult_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_5, type, diseqlist_0: ('list_0()' * 'list_0()') > $o).
tff(pred_def_6, type, store_0: ('list_0()' * 'list_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_7, type, fetch_0: ('Nat_0()' * 'list_0()' * 'Nat_0()') > $o).
tff(pred_def_8, type, eval_0: ('Nat_0()' * 'list_0()' * 'E_0()') > $o).
tff(pred_def_9, type, x_1: ('list_1()' * 'list_1()' * 'list_1()') > $o).
tff(pred_def_10, type, opti_0: ('P_0()' * 'P_0()') > $o).
tff(pred_def_11, type, run_0: ('list_0()' * 'list_0()' * 'list_1()') > $o).
tff(f574,plain,(
  $false),
  inference(avatar_sat_refutation,[],[f507,f527,f535,f553,f555,f566,f573])).
tff(f573,plain,(
  ~spl0_19),
  inference(avatar_contradiction_clause,[],[f567])).
tff(f567,plain,(
  $false | ~spl0_19),
  inference(resolution,[],[f552,f115])).
tff(f115,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'list_0()'] : (eval_0(X0,X1,'N_0'(X0))) )),
  inference(cnf_transformation,[],[f26])).
tff(f26,axiom,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()'] : eval_0(X0,X1,'N_0'(X0))),
  file('/home/columpio/RiderProjects/RInGen/samples/fast_unsat.FreeSorts.smt2',unknown)).
tff(f552,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'E_0()'] : (~eval_0(X0,nil_0,X1)) ) | ~spl0_19),
  inference(avatar_component_clause,[],[f551])).
tff(f551,plain,(
  spl0_19 <=> ! [X1 : 'E_0()',X0 : 'Nat_0()'] : ~eval_0(X0,nil_0,X1)),
  introduced(avatar_definition,[new_symbols(naming,[spl0_19])])).
tff(f566,plain,(
  spl0_17 | ~spl0_18),
  inference(avatar_split_clause,[],[f557,f548,f525])).
tff(f525,plain,(
  spl0_17 <=> ! [X9 : 'list_1()'] : ~x_1(nil_1,X9,nil_1)),
  introduced(avatar_definition,[new_symbols(naming,[spl0_17])])).
tff(f548,plain,(
  spl0_18 <=> ! [X3 : 'list_1()',X2 : 'list_0()',X4 : 'list_1()'] : (~run_0(X2,nil_0,X3) | ~x_1(X3,X4,nil_1))),
  introduced(avatar_definition,[new_symbols(naming,[spl0_18])])).
tff(f557,plain,(
  ( ! [X4 : 'list_1()'] : (~x_1(nil_1,X4,nil_1)) ) | ~spl0_18),
  inference(resolution,[],[f549,f108])).
tff(f108,plain,(
  ( ! [X0 : 'list_0()'] : (run_0(nil_0,X0,nil_1)) )),
  inference(cnf_transformation,[],[f38])).
tff(f38,axiom,(
  ! [X0 : 'list_0()'] : run_0(nil_0,X0,nil_1)),
  file('/home/columpio/RiderProjects/RInGen/samples/fast_unsat.FreeSorts.smt2',unknown)).
tff(f549,plain,(
  ( ! [X4 : 'list_1()',X2 : 'list_0()',X3 : 'list_1()'] : (~run_0(X2,nil_0,X3) | ~x_1(X3,X4,nil_1)) ) | ~spl0_18),
  inference(avatar_component_clause,[],[f548])).
tff(f555,plain,(
  ~spl0_17),
  inference(avatar_contradiction_clause,[],[f554])).
tff(f554,plain,(
  $false | ~spl0_17),
  inference(resolution,[],[f526,f110])).
tff(f110,plain,(
  ( ! [X0 : 'list_1()'] : (x_1(X0,nil_1,X0)) )),
  inference(cnf_transformation,[],[f28])).
tff(f28,axiom,(
  ! [X0 : 'list_1()'] : x_1(X0,nil_1,X0)),
  file('/home/columpio/RiderProjects/RInGen/samples/fast_unsat.FreeSorts.smt2',unknown)).
tff(f526,plain,(
  ( ! [X9 : 'list_1()'] : (~x_1(nil_1,X9,nil_1)) ) | ~spl0_17),
  inference(avatar_component_clause,[],[f525])).
tff(f553,plain,(
  spl0_18 | spl0_19 | ~spl0_16),
  inference(avatar_split_clause,[],[f546,f521,f551,f548])).
tff(f521,plain,(
  spl0_16 <=> ! [X1 : 'list_1()',X5 : 'list_0()',X0 : 'list_1()'] : (~x_1(X0,X1,nil_1) | ~diseqlist_0(nil_0,X5) | ~run_0(X5,nil_0,X0))),
  introduced(avatar_definition,[new_symbols(naming,[spl0_16])])).
tff(f546,plain,(
  ( ! [X4 : 'list_1()',X2 : 'list_0()',X0 : 'Nat_0()',X3 : 'list_1()',X1 : 'E_0()'] : (~eval_0(X0,nil_0,X1) | ~run_0(X2,nil_0,X3) | ~x_1(X3,X4,nil_1)) ) | ~spl0_16),
  inference(resolution,[],[f545,f127])).
tff(f127,plain,(
  ( ! [X2 : 'list_1()',X0 : 'list_1()',X3 : 'list_1()',X1 : 'P_0()'] : (x_1(cons_1(X1,X0),cons_1(X1,X2),X3) | ~x_1(X0,X2,X3)) )),
  inference(cnf_transformation,[],[f73])).
tff(f73,plain,(
  ! [X0 : 'list_1()',X1 : 'P_0()',X2 : 'list_1()',X3 : 'list_1()'] : (x_1(cons_1(X1,X0),cons_1(X1,X2),X3) | ~x_1(X0,X2,X3))),
  inference(ennf_transformation,[],[f27])).
tff(f27,axiom,(
  ! [X0 : 'list_1()',X1 : 'P_0()',X2 : 'list_1()',X3 : 'list_1()'] : (x_1(X0,X2,X3) => x_1(cons_1(X1,X0),cons_1(X1,X2),X3))),
  file('/home/columpio/RiderProjects/RInGen/samples/fast_unsat.FreeSorts.smt2',unknown)).
tff(f545,plain,(
  ( ! [X6 : 'list_0()',X8 : 'list_1()',X7 : 'E_0()',X5 : 'Nat_0()',X9 : 'list_1()'] : (~x_1(cons_1('Print_0'(X7),X8),X9,nil_1) | ~eval_0(X5,nil_0,X7) | ~run_0(X6,nil_0,X8)) ) | ~spl0_16),
  inference(subsumption_resolution,[],[f538,f113])).
tff(f113,plain,(
  ( ! [X0 : 'list_0()',X1 : 'Nat_0()'] : (diseqlist_0(nil_0,cons_0(X1,X0))) )),
  inference(cnf_transformation,[],[f41])).
tff(f41,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()'] : diseqlist_0(nil_0,cons_0(X1,X0))),
  inference(rectify,[],[f10])).
tff(f10,axiom,(
  ! [X1 : 'list_0()',X0 : 'Nat_0()'] : diseqlist_0(nil_0,cons_0(X0,X1))),
  file('/home/columpio/RiderProjects/RInGen/samples/fast_unsat.FreeSorts.smt2',unknown)).
tff(f538,plain,(
  ( ! [X6 : 'list_0()',X8 : 'list_1()',X7 : 'E_0()',X5 : 'Nat_0()',X9 : 'list_1()'] : (~diseqlist_0(nil_0,cons_0(X5,X6)) | ~x_1(cons_1('Print_0'(X7),X8),X9,nil_1) | ~eval_0(X5,nil_0,X7) | ~run_0(X6,nil_0,X8)) ) | ~spl0_16),
  inference(resolution,[],[f522,f132])).
tff(f132,plain,(
  ( ! [X4 : 'Nat_0()',X2 : 'E_0()',X0 : 'list_1()',X3 : 'list_0()',X1 : 'list_0()'] : (run_0(cons_0(X4,X3),X1,cons_1('Print_0'(X2),X0)) | ~eval_0(X4,X1,X2) | ~run_0(X3,X1,X0)) )),
  inference(cnf_transformation,[],[f82])).
tff(f82,plain,(
  ! [X0 : 'list_1()',X1 : 'list_0()',X2 : 'E_0()',X3 : 'list_0()',X4 : 'Nat_0()'] : (run_0(cons_0(X4,X3),X1,cons_1('Print_0'(X2),X0)) | ~eval_0(X4,X1,X2) | ~run_0(X3,X1,X0))),
  inference(flattening,[],[f81])).
tff(f81,plain,(
  ! [X0 : 'list_1()',X1 : 'list_0()',X2 : 'E_0()',X3 : 'list_0()',X4 : 'Nat_0()'] : (run_0(cons_0(X4,X3),X1,cons_1('Print_0'(X2),X0)) | (~eval_0(X4,X1,X2) | ~run_0(X3,X1,X0)))),
  inference(ennf_transformation,[],[f56])).
tff(f56,plain,(
  ! [X0 : 'list_1()',X1 : 'list_0()',X2 : 'E_0()',X3 : 'list_0()',X4 : 'Nat_0()'] : ((eval_0(X4,X1,X2) & run_0(X3,X1,X0)) => run_0(cons_0(X4,X3),X1,cons_1('Print_0'(X2),X0)))),
  inference(rectify,[],[f37])).
tff(f37,axiom,(
  ! [X3 : 'list_1()',X4 : 'list_0()',X2 : 'E_0()',X1 : 'list_0()',X0 : 'Nat_0()'] : ((eval_0(X0,X4,X2) & run_0(X1,X4,X3)) => run_0(cons_0(X0,X1),X4,cons_1('Print_0'(X2),X3)))),
  file('/home/columpio/RiderProjects/RInGen/samples/fast_unsat.FreeSorts.smt2',unknown)).
tff(f522,plain,(
  ( ! [X0 : 'list_1()',X5 : 'list_0()',X1 : 'list_1()'] : (~run_0(X5,nil_0,X0) | ~diseqlist_0(nil_0,X5) | ~x_1(X0,X1,nil_1)) ) | ~spl0_16),
  inference(avatar_component_clause,[],[f521])).
tff(f535,plain,(
  ~spl0_14),
  inference(avatar_contradiction_clause,[],[f534])).
tff(f534,plain,(
  $false | ~spl0_14),
  inference(subsumption_resolution,[],[f532,f107])).
tff(f107,plain,(
  ( ! [X0 : 'Nat_0()'] : (fetch_0('Z_0',nil_0,X0)) )),
  inference(cnf_transformation,[],[f20])).
tff(f20,axiom,(
  ! [X0 : 'Nat_0()'] : fetch_0('Z_0',nil_0,X0)),
  file('/home/columpio/RiderProjects/RInGen/samples/fast_unsat.FreeSorts.smt2',unknown)).
tff(f532,plain,(
  ( ! [X12 : 'Nat_0()'] : (~fetch_0('Z_0',nil_0,X12)) ) | ~spl0_14),
  inference(resolution,[],[f506,f124])).
tff(f124,plain,(
  ( ! [X2 : 'list_0()',X0 : 'Nat_0()',X1 : 'Nat_0()'] : (eval_0(X1,X2,'V_0'(X0)) | ~fetch_0(X1,X2,X0)) )),
  inference(cnf_transformation,[],[f70])).
tff(f70,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'list_0()'] : (eval_0(X1,X2,'V_0'(X0)) | ~fetch_0(X1,X2,X0))),
  inference(ennf_transformation,[],[f48])).
tff(f48,plain,(
  ! [X0 : 'Nat_0()',X1 : 'Nat_0()',X2 : 'list_0()'] : (fetch_0(X1,X2,X0) => eval_0(X1,X2,'V_0'(X0)))),
  inference(rectify,[],[f21])).
tff(f21,axiom,(
  ! [X1 : 'Nat_0()',X0 : 'Nat_0()',X2 : 'list_0()'] : (fetch_0(X0,X2,X1) => eval_0(X0,X2,'V_0'(X1)))),
  file('/home/columpio/RiderProjects/RInGen/samples/fast_unsat.FreeSorts.smt2',unknown)).
tff(f506,plain,(
  ( ! [X0 : 'E_0()'] : (~eval_0('Z_0',nil_0,X0)) ) | ~spl0_14),
  inference(avatar_component_clause,[],[f505])).
tff(f505,plain,(
  spl0_14 <=> ! [X0 : 'E_0()'] : ~eval_0('Z_0',nil_0,X0)),
  introduced(avatar_definition,[new_symbols(naming,[spl0_14])])).
tff(f527,plain,(
  spl0_17 | spl0_16 | ~spl0_13),
  inference(avatar_split_clause,[],[f509,f502,f521,f525])).
tff(f502,plain,(
  spl0_13 <=> ! [X1 : 'list_1()',X3 : 'list_0()',X5 : 'list_1()',X2 : 'list_1()',X4 : 'list_0()',X6 : 'list_1()'] : (~x_1(X1,X2,nil_1) | ~run_0(X4,nil_0,X5) | ~x_1(X5,X6,nil_1) | ~diseqlist_0(X4,X3) | ~run_0(X3,nil_0,X1))),
  introduced(avatar_definition,[new_symbols(naming,[spl0_13])])).
tff(f509,plain,(
  ( ! [X10 : 'list_0()',X8 : 'list_1()',X7 : 'list_1()',X9 : 'list_1()'] : (~x_1(X7,X8,nil_1) | ~x_1(nil_1,X9,nil_1) | ~diseqlist_0(nil_0,X10) | ~run_0(X10,nil_0,X7)) ) | ~spl0_13),
  inference(resolution,[],[f503,f108])).
tff(f503,plain,(
  ( ! [X6 : 'list_1()',X4 : 'list_0()',X2 : 'list_1()',X5 : 'list_1()',X3 : 'list_0()',X1 : 'list_1()'] : (~run_0(X4,nil_0,X5) | ~x_1(X1,X2,nil_1) | ~x_1(X5,X6,nil_1) | ~diseqlist_0(X4,X3) | ~run_0(X3,nil_0,X1)) ) | ~spl0_13),
  inference(avatar_component_clause,[],[f502])).
tff(f507,plain,(
  spl0_13 | spl0_14),
  inference(avatar_split_clause,[],[f500,f505,f502])).
tff(f500,plain,(
  ( ! [X6 : 'list_1()',X4 : 'list_0()',X2 : 'list_1()',X0 : 'E_0()',X5 : 'list_1()',X3 : 'list_0()',X1 : 'list_1()'] : (~eval_0('Z_0',nil_0,X0) | ~x_1(X1,X2,nil_1) | ~run_0(X3,nil_0,X1) | ~diseqlist_0(X4,X3) | ~x_1(X5,X6,nil_1) | ~run_0(X4,nil_0,X5)) )),
  inference(duplicate_literal_removal,[],[f499])).
tff(f499,plain,(
  ( ! [X6 : 'list_1()',X4 : 'list_0()',X2 : 'list_1()',X0 : 'E_0()',X5 : 'list_1()',X3 : 'list_0()',X1 : 'list_1()'] : (~eval_0('Z_0',nil_0,X0) | ~x_1(X1,X2,nil_1) | ~run_0(X3,nil_0,X1) | ~diseqlist_0(X4,X3) | ~x_1(X5,X6,nil_1) | ~run_0(X4,nil_0,X5) | ~eval_0('Z_0',nil_0,X0)) )),
  inference(resolution,[],[f169,f119])).
tff(f119,plain,(
  ( ! [X2 : 'E_0()',X0 : 'list_1()',X1 : 'list_1()'] : (opti_0('If_0'(X2,X1,X0),'If_0'(X2,X0,X1))) )),
  inference(cnf_transformation,[],[f44])).
tff(f44,plain,(
  ! [X0 : 'list_1()',X1 : 'list_1()',X2 : 'E_0()'] : opti_0('If_0'(X2,X1,X0),'If_0'(X2,X0,X1))),
  inference(rectify,[],[f29])).
tff(f29,axiom,(
  ! [X1 : 'list_1()',X2 : 'list_1()',X0 : 'E_0()'] : opti_0('If_0'(X0,X2,X1),'If_0'(X0,X1,X2))),
  file('/home/columpio/RiderProjects/RInGen/samples/fast_unsat.FreeSorts.smt2',unknown)).
tff(f169,plain,(
  ( ! [X30 : 'list_1()',X28 : 'list_1()',X35 : 'list_0()',X33 : 'list_1()',X31 : 'list_1()',X29 : 'E_0()',X27 : 'list_0()',X36 : 'list_1()',X34 : 'list_1()',X32 : 'E_0()'] : (~opti_0('If_0'(X29,X31,X30),'If_0'(X32,X33,X34)) | ~eval_0('Z_0',nil_0,X29) | ~x_1(X28,X30,nil_1) | ~run_0(X27,nil_0,X28) | ~diseqlist_0(X35,X27) | ~x_1(X36,X34,nil_1) | ~run_0(X35,nil_0,X36) | ~eval_0('Z_0',nil_0,X32)) )),
  inference(resolution,[],[f147,f139])).
tff(f139,plain,(
  ( ! [X6 : 'list_1()',X4 : 'list_0()',X2 : 'list_0()',X0 : 'list_1()',X5 : 'list_1()',X3 : 'list_1()',X1 : 'E_0()'] : (run_0(X2,X4,cons_1('If_0'(X1,X0,X6),X5)) | ~x_1(X3,X6,X5) | ~run_0(X2,X4,X3) | ~eval_0('Z_0',X4,X1)) )),
  inference(cnf_transformation,[],[f96])).
tff(f96,plain,(
  ! [X0 : 'list_1()',X1 : 'E_0()',X2 : 'list_0()',X3 : 'list_1()',X4 : 'list_0()',X5 : 'list_1()',X6 : 'list_1()'] : (run_0(X2,X4,cons_1('If_0'(X1,X0,X6),X5)) | ~x_1(X3,X6,X5) | ~run_0(X2,X4,X3) | ~eval_0('Z_0',X4,X1))),
  inference(flattening,[],[f95])).
tff(f95,plain,(
  ! [X0 : 'list_1()',X1 : 'E_0()',X2 : 'list_0()',X3 : 'list_1()',X4 : 'list_0()',X5 : 'list_1()',X6 : 'list_1()'] : (run_0(X2,X4,cons_1('If_0'(X1,X0,X6),X5)) | (~x_1(X3,X6,X5) | ~run_0(X2,X4,X3) | ~eval_0('Z_0',X4,X1)))),
  inference(ennf_transformation,[],[f63])).
tff(f63,plain,(
  ! [X0 : 'list_1()',X1 : 'E_0()',X2 : 'list_0()',X3 : 'list_1()',X4 : 'list_0()',X5 : 'list_1()',X6 : 'list_1()'] : ((x_1(X3,X6,X5) & run_0(X2,X4,X3) & eval_0('Z_0',X4,X1)) => run_0(X2,X4,cons_1('If_0'(X1,X0,X6),X5)))),
  inference(rectify,[],[f33])).
tff(f33,axiom,(
  ! [X3 : 'list_1()',X2 : 'E_0()',X0 : 'list_0()',X1 : 'list_1()',X6 : 'list_0()',X5 : 'list_1()',X4 : 'list_1()'] : ((x_1(X1,X4,X5) & run_0(X0,X6,X1) & eval_0('Z_0',X6,X2)) => run_0(X0,X6,cons_1('If_0'(X2,X3,X4),X5)))),
  file('/home/columpio/RiderProjects/RInGen/samples/fast_unsat.FreeSorts.smt2',unknown)).
tff(f147,plain,(
  ( ! [X6 : 'list_1()',X4 : 'list_0()',X2 : 'list_0()',X0 : 'list_1()',X5 : 'P_0()',X3 : 'E_0()',X1 : 'list_1()'] : (~run_0(X4,nil_0,cons_1(X5,nil_1)) | ~run_0(X2,nil_0,X0) | ~eval_0('Z_0',nil_0,X3) | ~x_1(X0,X1,nil_1) | ~opti_0('If_0'(X3,X6,X1),X5) | ~diseqlist_0(X4,X2)) )),
  inference(resolution,[],[f139,f131])).
tff(f131,plain,(
  ( ! [X2 : 'list_0()',X0 : 'list_0()',X3 : 'P_0()',X1 : 'P_0()'] : (~run_0(X2,nil_0,cons_1(X3,nil_1)) | ~run_0(X0,nil_0,cons_1(X1,nil_1)) | ~opti_0(X3,X1) | ~diseqlist_0(X0,X2)) )),
  inference(cnf_transformation,[],[f80])).
tff(f80,plain,(
  ! [X0 : 'list_0()',X1 : 'P_0()',X2 : 'list_0()',X3 : 'P_0()'] : (~diseqlist_0(X0,X2) | ~run_0(X0,nil_0,cons_1(X1,nil_1)) | ~opti_0(X3,X1) | ~run_0(X2,nil_0,cons_1(X3,nil_1)))),
  inference(ennf_transformation,[],[f55])).
tff(f55,plain,(
  ! [X0 : 'list_0()',X1 : 'P_0()',X2 : 'list_0()',X3 : 'P_0()'] : ~(diseqlist_0(X0,X2) & run_0(X0,nil_0,cons_1(X1,nil_1)) & opti_0(X3,X1) & run_0(X2,nil_0,cons_1(X3,nil_1)))),
  inference(true_and_false_elimination,[],[f54])).
tff(f54,plain,(
  ! [X0 : 'list_0()',X1 : 'P_0()',X2 : 'list_0()',X3 : 'P_0()'] : ((diseqlist_0(X0,X2) & run_0(X0,nil_0,cons_1(X1,nil_1)) & opti_0(X3,X1) & run_0(X2,nil_0,cons_1(X3,nil_1))) => $false)),
  inference(rectify,[],[f39])).
tff(f39,axiom,(
  ! [X0 : 'list_0()',X3 : 'P_0()',X2 : 'list_0()',X1 : 'P_0()'] : ((diseqlist_0(X0,X2) & run_0(X0,nil_0,cons_1(X3,nil_1)) & opti_0(X1,X3) & run_0(X2,nil_0,cons_1(X1,nil_1))) => $false)),
  file('/home/columpio/RiderProjects/RInGen/samples/fast_unsat.FreeSorts.smt2',unknown)).
