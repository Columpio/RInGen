11
17220
260
UNKNOWN % Warning: check-sat is not the last entry. Skipping the rest!
% ott+10_128_av=off:bs=on:gsp=input_only:irw=on:lcm=predicate:lma=on:nm=0:nwc=1:sp=occurrence:urr=on:updr=off:uhcvi=on_4 on weird_nat_mul3_same
% Refutation found. Thanks to Tanya!
% SZS status Unsatisfiable for weird_nat_mul3_same
% SZS output start Proof for weird_nat_mul3_same
tff(type_def_5, type, 'Nat_0()': $tType).
tff(func_def_0, type, zero_0: 'Nat_0()').
tff(func_def_1, type, succ_0: ('Nat_0()') > 'Nat_0()').
tff(pred_def_1, type, diseqNat_0: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_2, type, p_1: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_3, type, iszero_0: ('Nat_0()') > $o).
tff(pred_def_4, type, issucc_0: ('Nat_0()') > $o).
tff(pred_def_5, type, plus_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_6, type, addacc_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_7, type, mulacc_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_8, type, add_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_9, type, mul_0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_10, type, sP0: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_11, type, sP1: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_12, type, sP2: ('Nat_0()') > $o).
tff(pred_def_13, type, sP3: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_14, type, sP4: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_15, type, sP5: ('Nat_0()') > $o).
tff(pred_def_16, type, sP6: ('Nat_0()') > $o).
tff(pred_def_17, type, sP7: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_18, type, sP8: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_19, type, sP9: ('Nat_0()') > $o).
tff(pred_def_20, type, sP10: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_21, type, sP11: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_22, type, sP12: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_23, type, sP13: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_24, type, sP14: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_25, type, sP15: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_26, type, sP16: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_27, type, sP17: ('Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_28, type, sP18: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_29, type, sP19: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_30, type, sP20: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_31, type, sP21: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_32, type, sP22: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_33, type, sP23: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_34, type, sP24: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_35, type, sP25: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_36, type, sP26: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_37, type, sP27: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_38, type, sP28: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_39, type, sP29: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_40, type, sP30: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_41, type, sP31: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_42, type, sP32: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_43, type, sP33: ('Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_44, type, sP34: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_45, type, sP35: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_46, type, sP36: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_47, type, sP37: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_48, type, sP38: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_49, type, sP39: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_50, type, sP40: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_51, type, sP41: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_52, type, sP42: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_53, type, sP43: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_54, type, sP44: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_55, type, sP45: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_56, type, sP46: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_57, type, sP47: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_58, type, sP48: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_59, type, sP49: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_60, type, sP50: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_61, type, sP51: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_62, type, sP52: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_63, type, sP53: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_64, type, sP54: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_65, type, sP55: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_66, type, sP56: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_67, type, sP57: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_68, type, sP58: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_69, type, sP59: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_70, type, sP60: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_71, type, sP61: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_72, type, sP62: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_73, type, sP63: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_74, type, sP64: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(pred_def_75, type, sP65: ('Nat_0()' * 'Nat_0()' * 'Nat_0()' * 'Nat_0()') > $o).
tff(f17322,plain,(
  $false),
  inference(unit_resulting_resolution,[],[f2915,f123,f129,f16135,f127,f574,f196])).
tff(f196,plain,(
  ( ! [X6 : 'Nat_0()',X4 : 'Nat_0()',X2 : 'Nat_0()',X3 : 'Nat_0()',X1 : 'Nat_0()'] : (~addacc_0(X4,succ_0(zero_0),succ_0(zero_0),succ_0(X3)) | ~mulacc_0(X6,zero_0,zero_0,X3) | ~diseqNat_0(X3,zero_0) | ~addacc_0(X1,X6,X2,X4) | ~sP14(X3,X1) | ~sP17(X3,X2)) )),
  inference(general_splitting,[],[f194,f195_D])).
tff(f195,plain,(
  ( ! [X2 : 'Nat_0()',X5 : 'Nat_0()',X3 : 'Nat_0()'] : (~mulacc_0(X5,succ_0(zero_0),zero_0,X3) | ~sP16(X5,X3,X2) | sP17(X3,X2)) )),
  inference(cnf_transformation,[],[f195_D])).
tff(f195_D,plain,(
  ( ! [X2,X3] : (( ! [X5] : (~mulacc_0(X5,succ_0(zero_0),zero_0,X3) | ~sP16(X5,X3,X2)) ) <=> ~sP17(X3,X2)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP17])])).
tff(f194,plain,(
  ( ! [X6 : 'Nat_0()',X4 : 'Nat_0()',X2 : 'Nat_0()',X5 : 'Nat_0()',X3 : 'Nat_0()',X1 : 'Nat_0()'] : (~diseqNat_0(X3,zero_0) | ~mulacc_0(X6,zero_0,zero_0,X3) | ~mulacc_0(X5,succ_0(zero_0),zero_0,X3) | ~addacc_0(X4,succ_0(zero_0),succ_0(zero_0),succ_0(X3)) | ~addacc_0(X1,X6,X2,X4) | ~sP14(X3,X1) | ~sP16(X5,X3,X2)) )),
  inference(general_splitting,[],[f192,f193_D])).
tff(f193,plain,(
  ( ! [X2 : 'Nat_0()',X8 : 'Nat_0()',X5 : 'Nat_0()',X3 : 'Nat_0()'] : (~mulacc_0(X8,zero_0,succ_0(zero_0),X3) | ~sP15(X8,X5,X2) | sP16(X5,X3,X2)) )),
  inference(cnf_transformation,[],[f193_D])).
tff(f193_D,plain,(
  ( ! [X2,X3,X5] : (( ! [X8] : (~mulacc_0(X8,zero_0,succ_0(zero_0),X3) | ~sP15(X8,X5,X2)) ) <=> ~sP16(X5,X3,X2)) )),
  introduced(general_splitting_component_introduction,[new_symbols(naming,[sP16])])).
tff(f192,plain,(
