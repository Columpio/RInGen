6
65156
2460
UNSAT
% lrs+2_1_lcm=predicate_20 on tmpZM6h4L.
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
tff(f58359,plain,(
  $false),
  inference(avatar_sat_refutation,[],[f4451,f56964,f56966,f58358])).
tff(f58358,plain,(
  ~spl0_129),
  inference(avatar_contradiction_clause,[],[f58357])).
tff(f58357,plain,(
  $false | ~spl0_129),
  inference(subsumption_resolution,[],[f58344,f107])).
tff(f107,plain,(
  ( ! [X0 : 'Nat_0()'] : (fetch_0('Z_0',nil_0,X0)) )),
  inference(cnf_transformation,[],[f20])).
tff(f20,axiom,(
  ! [X0 : 'Nat_0()'] : fetch_0('Z_0',nil_0,X0)),
  file('/tmp/tmpZM6h4L..smt2',unknown)).
tff(f58344,plain,(
  ( ! [X7433 : 'Nat_0()'] : (~fetch_0('Z_0',nil_0,X7433)) ) | ~spl0_129),
  inference(resolution,[],[f56963,f124])).
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
  file('/tmp/tmpZM6h4L..smt2',unknown)).
tff(f56963,plain,(
  ( ! [X0 : 'E_0()'] : (~eval_0('Z_0',nil_0,X0)) ) | ~spl0_129),
  inference(avatar_component_clause,[],[f56962])).
tff(f56962,plain,(
  spl0_129 <=> ! [X0 : 'E_0()'] : ~eval_0('Z_0',nil_0,X0)),
  introduced(avatar_definition,[new_symbols(naming,[spl0_129])])).
tff(f56966,plain,(
  ~spl0_128),
  inference(avatar_contradiction_clause,[],[f56965])).
tff(f56965,plain,(
  $false | ~spl0_128),
  inference(resolution,[],[f56960,f110])).
tff(f110,plain,(
  ( ! [X0 : 'list_1()'] : (x_1(X0,nil_1,X0)) )),
  inference(cnf_transformation,[],[f28])).
tff(f28,axiom,(
  ! [X0 : 'list_1()'] : x_1(X0,nil_1,X0)),
  file('/tmp/tmpZM6h4L..smt2',unknown)).
tff(f56960,plain,(
  ( ! [X2 : 'list_1()'] : (~x_1(nil_1,X2,nil_1)) ) | ~spl0_128),
  inference(avatar_component_clause,[],[f56959])).
tff(f56959,plain,(
  spl0_128 <=> ! [X2 : 'list_1()'] : ~x_1(nil_1,X2,nil_1)),
  introduced(avatar_definition,[new_symbols(naming,[spl0_128])])).
tff(f56964,plain,(
  spl0_34 | spl0_128 | spl0_128 | spl0_129),
  inference(avatar_split_clause,[],[f56957,f56962,f56959,f56959,f4190])).
tff(f4190,plain,(
  spl0_34 <=> ! [X228 : 'E_0()',X227 : 'Nat_0()'] : ~eval_0(X227,nil_0,X228)),
  introduced(avatar_definition,[new_symbols(naming,[spl0_34])])).
tff(f56957,plain,(
  ( ! [X4 : 'E_0()',X2 : 'list_1()',X0 : 'E_0()',X3 : 'Nat_0()',X1 : 'list_1()'] : (~eval_0('Z_0',nil_0,X0) | ~x_1(nil_1,X1,nil_1) | ~x_1(nil_1,X2,nil_1) | ~eval_0(X3,nil_0,X4)) )),
  inference(duplicate_literal_removal,[],[f56956])).
tff(f56956,plain,(
  ( ! [X4 : 'E_0()',X2 : 'list_1()',X0 : 'E_0()',X3 : 'Nat_0()',X1 : 'list_1()'] : (~eval_0('Z_0',nil_0,X0) | ~x_1(nil_1,X1,nil_1) | ~eval_0('Z_0',nil_0,X0) | ~x_1(nil_1,X2,nil_1) | ~eval_0(X3,nil_0,X4)) )),
  inference(resolution,[],[f10028,f119])).
tff(f119,plain,(
  ( ! [X2 : 'E_0()',X0 : 'list_1()',X1 : 'list_1()'] : (opti_0('If_0'(X2,X1,X0),'If_0'(X2,X0,X1))) )),
  inference(cnf_transformation,[],[f44])).
tff(f44,plain,(
  ! [X0 : 'list_1()',X1 : 'list_1()',X2 : 'E_0()'] : opti_0('If_0'(X2,X1,X0),'If_0'(X2,X0,X1))),
  inference(rectify,[],[f29])).
tff(f29,axiom,(
  ! [X1 : 'list_1()',X2 : 'list_1()',X0 : 'E_0()'] : opti_0('If_0'(X0,X2,X1),'If_0'(X0,X1,X2))),
  file('/tmp/tmpZM6h4L..smt2',unknown)).
tff(f10028,plain,(
  ( ! [X14 : 'list_1()',X12 : 'list_1()',X10 : 'E_0()',X15 : 'list_1()',X13 : 'E_0()',X11 : 'E_0()',X9 : 'Nat_0()',X16 : 'list_1()'] : (~opti_0('If_0'(X13,X15,X14),'If_0'(X11,X16,cons_1('Print_0'(X10),X12))) | ~eval_0('Z_0',nil_0,X11) | ~x_1(nil_1,X12,nil_1) | ~eval_0('Z_0',nil_0,X13) | ~x_1(nil_1,X14,nil_1) | ~eval_0(X9,nil_0,X10)) )),
  inference(subsumption_resolution,[],[f10012,f114])).
tff(f114,plain,(
  ( ! [X0 : 'list_0()',X1 : 'Nat_0()'] : (diseqlist_0(cons_0(X1,X0),nil_0)) )),
  inference(cnf_transformation,[],[f42])).
tff(f42,plain,(
  ! [X0 : 'list_0()',X1 : 'Nat_0()'] : diseqlist_0(cons_0(X1,X0),nil_0)),
  inference(rectify,[],[f11])).
tff(f11,axiom,(
  ! [X1 : 'list_0()',X0 : 'Nat_0()'] : diseqlist_0(cons_0(X0,X1),nil_0)),
  file('/tmp/tmpZM6h4L..smt2',unknown)).
tff(f10012,plain,(
  ( ! [X14 : 'list_1()',X12 : 'list_1()',X10 : 'E_0()',X15 : 'list_1()',X13 : 'E_0()',X11 : 'E_0()',X9 : 'Nat_0()',X16 : 'list_1()'] : (~eval_0(X9,nil_0,X10) | ~eval_0('Z_0',nil_0,X11) | ~x_1(nil_1,X12,nil_1) | ~eval_0('Z_0',nil_0,X13) | ~x_1(nil_1,X14,nil_1) | ~opti_0('If_0'(X13,X15,X14),'If_0'(X11,X16,cons_1('Print_0'(X10),X12))) | ~diseqlist_0(cons_0(X9,nil_0),nil_0)) )),
  inference(resolution,[],[f1115,f247])).
tff(f247,plain,(
  ( ! [X4 : 'list_1()',X2 : 'list_0()',X0 : 'list_1()',X3 : 'P_0()',X1 : 'E_0()'] : (~run_0(X2,nil_0,cons_1(X3,nil_1)) | ~eval_0('Z_0',nil_0,X1) | ~x_1(nil_1,X0,nil_1) | ~opti_0('If_0'(X1,X4,X0),X3) | ~diseqlist_0(X2,nil_0)) )),
  inference(resolution,[],[f190,f131])).
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
  file('/tmp/tmpZM6h4L..smt2',unknown)).
tff(f190,plain,(
  ( ! [X4 : 'list_1()',X2 : 'list_0()',X0 : 'list_1()',X3 : 'E_0()',X1 : 'list_1()'] : (run_0(nil_0,X2,cons_1('If_0'(X3,X4,X0),X1)) | ~x_1(nil_1,X0,X1) | ~eval_0('Z_0',X2,X3)) )),
  inference(resolution,[],[f139,f108])).
tff(f108,plain,(
  ( ! [X0 : 'list_0()'] : (run_0(nil_0,X0,nil_1)) )),
  inference(cnf_transformation,[],[f38])).
tff(f38,axiom,(
  ! [X0 : 'list_0()'] : run_0(nil_0,X0,nil_1)),
  file('/tmp/tmpZM6h4L..smt2',unknown)).
tff(f139,plain,(
  ( ! [X6 : 'list_1()',X4 : 'list_0()',X2 : 'list_0()',X0 : 'list_1()',X5 : 'list_1()',X3 : 'list_1()',X1 : 'E_0()'] : (~run_0(X2,X4,X3) | ~x_1(X3,X6,X5) | run_0(X2,X4,cons_1('If_0'(X1,X0,X6),X5)) | ~eval_0('Z_0',X4,X1)) )),
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
  file('/tmp/tmpZM6h4L..smt2',unknown)).
tff(f1115,plain,(
  ( ! [X6 : 'list_1()',X4 : 'list_1()',X2 : 'Nat_0()',X0 : 'list_0()',X5 : 'list_1()',X3 : 'E_0()',X1 : 'E_0()'] : (run_0(cons_0(X2,nil_0),X0,cons_1('If_0'(X1,X4,cons_1('Print_0'(X3),X5)),X6)) | ~eval_0(X2,X0,X3) | ~eval_0('Z_0',X0,X1) | ~x_1(nil_1,X5,X6)) )),
  inference(resolution,[],[f402,f108])).
tff(f402,plain,(
  ( ! [X6 : 'list_1()',X4 : 'list_1()',X2 : 'list_0()',X0 : 'Nat_0()',X8 : 'list_1()',X7 : 'list_1()',X5 : 'E_0()',X3 : 'E_0()',X1 : 'list_0()'] : (~run_0(X1,X2,X8) | ~eval_0('Z_0',X2,X3) | ~eval_0(X0,X2,X5) | run_0(cons_0(X0,X1),X2,cons_1('If_0'(X3,X4,cons_1('Print_0'(X5),X6)),X7)) | ~x_1(X8,X6,X7)) )),
  inference(resolution,[],[f191,f127])).
tff(f127,plain,(
  ( ! [X2 : 'list_1()',X0 : 'list_1()',X3 : 'list_1()',X1 : 'P_0()'] : (x_1(cons_1(X1,X0),cons_1(X1,X2),X3) | ~x_1(X0,X2,X3)) )),
  inference(cnf_transformation,[],[f73])).
tff(f73,plain,(
  ! [X0 : 'list_1()',X1 : 'P_0()',X2 : 'list_1()',X3 : 'list_1()'] : (x_1(cons_1(X1,X0),cons_1(X1,X2),X3) | ~x_1(X0,X2,X3))),
  inference(ennf_transformation,[],[f27])).
tff(f27,axiom,(
  ! [X0 : 'list_1()',X1 : 'P_0()',X2 : 'list_1()',X3 : 'list_1()'] : (x_1(X0,X2,X3) => x_1(cons_1(X1,X0),cons_1(X1,X2),X3))),
  file('/tmp/tmpZM6h4L..smt2',unknown)).
tff(f191,plain,(
  ( ! [X6 : 'list_1()',X12 : 'E_0()',X10 : 'list_0()',X8 : 'list_1()',X7 : 'list_1()',X5 : 'E_0()',X13 : 'list_1()',X11 : 'list_0()',X9 : 'Nat_0()'] : (~x_1(cons_1('Print_0'(X5),X6),X7,X8) | run_0(cons_0(X9,X10),X11,cons_1('If_0'(X12,X13,X7),X8)) | ~eval_0('Z_0',X11,X12) | ~eval_0(X9,X11,X5) | ~run_0(X10,X11,X6)) )),
  inference(resolution,[],[f139,f132])).
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
  file('/tmp/tmpZM6h4L..smt2',unknown)).
tff(f4451,plain,(
  ~spl0_34),
  inference(avatar_contradiction_clause,[],[f4343])).
tff(f4343,plain,(
  $false | ~spl0_34),
  inference(resolution,[],[f4191,f115])).
tff(f115,plain,(
  ( ! [X0 : 'Nat_0()',X1 : 'list_0()'] : (eval_0(X0,X1,'N_0'(X0))) )),
  inference(cnf_transformation,[],[f26])).
tff(f26,axiom,(
  ! [X0 : 'Nat_0()',X1 : 'list_0()'] : eval_0(X0,X1,'N_0'(X0))),
  file('/tmp/tmpZM6h4L..smt2',unknown)).
tff(f4191,plain,(
  ( ! [X227 : 'Nat_0()',X228 : 'E_0()'] : (~eval_0(X227,nil_0,X228)) ) | ~spl0_34),
  inference(avatar_component_clause,[],[f4190])).
