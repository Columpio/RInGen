7
34764
860
UNKNOWN % Warning: check-sat is not the last entry. Skipping the rest!
% ott+10_128_av=off:bs=on:gsp=input_only:irw=on:lcm=predicate:lma=on:nm=0:nwc=1:sp=occurrence:urr=on:updr=off:uhcvi=on_4 on escape_NoSpecial
% Time limit reached!
% ------------------------------
% Version: Vampire 4.6.1 (commit af1735c99 on 2021-12-01 14:43:47 +0100)
% Linked with Z3 4.8.13.0 f03d756e086f81f2596157241e0decfb1c982299 z3-4.8.4-5390-gf03d756e0
% Termination reason: Time limit
% Termination phase: Saturation

% Memory used [KB]: 24818
% Time elapsed: 0.800 s
% ------------------------------
% ------------------------------
% fmb+10_1_av=off:bce=on:nm=6_1461 on escape_NoSpecial
TRYING [1]
TRYING [2]
TRYING [3]
Finite Model Found!
% SZS status Satisfiable for escape_NoSpecial
% SZS output start FiniteModel for escape_NoSpecial
tff(declare_$i,type,$i:$tType).
tff(declare_$i1,type,fmb_$i_1:$i).
tff(finite_domain,axiom,
      ! [X:$i] : (
         X = fmb_$i_1
      ) ).

tff(declare_bool,type,$o:$tType).
tff(declare_bool1,type,fmb_bool_1:$o).
tff(finite_domain,axiom,
      ! [X:$o] : (
         X = fmb_bool_1
      ) ).

tff('declare_Bool_0()',type,'Bool_0()':$tType).
tff('declare_Bool_0()1',type,false_0:'Bool_0()').
tff('declare_Bool_0()2',type,true_0:'Bool_0()').
tff('declare_Bool_0()3',type,fmb_'Bool_0()'_3:'Bool_0()').
tff(finite_domain,axiom,
      ! [X:'Bool_0()'] : (
         X = false_0 | X = true_0 | X = fmb_'Bool_0()'_3
      ) ).

tff(distinct_domain,axiom,
         false_0 != true_0 & false_0 != fmb_'Bool_0()'_3 & true_0 != fmb_'Bool_0()'_3
).

tff('declare_Token_0()',type,'Token_0()':$tType).
tff('declare_Token_0()1',type,'A_0':'Token_0()').
tff('declare_Token_0()2',type,'ESC_0':'Token_0()').
tff('declare_Token_0()3',type,'P_0':'Token_0()').
tff(finite_domain,axiom,
      ! [X:'Token_0()'] : (
         X = 'A_0' | X = 'ESC_0' | X = 'P_0'
      ) ).

tff(distinct_domain,axiom,
         'A_0' != 'ESC_0' & 'A_0' != 'P_0' & 'ESC_0' != 'P_0'
).

tff('declare_list_0()',type,'list_0()':$tType).
tff('declare_list_0()1',type,nil_0:'list_0()').
tff('declare_list_0()2',type,fmb_'list_0()'_2:'list_0()').
tff('declare_list_0()3',type,fmb_'list_0()'_3:'list_0()').
tff(finite_domain,axiom,
      ! [X:'list_0()'] : (
         X = nil_0 | X = fmb_'list_0()'_2 | X = fmb_'list_0()'_3
      ) ).

tff(distinct_domain,axiom,
         nil_0 != fmb_'list_0()'_2 & nil_0 != fmb_'list_0()'_3 & fmb_'list_0()'_2 != fmb_'list_0()'_3
).

tff('declare_B_0',type,'B_0':'Token_0()').
tff('B_0_definition',axiom,'B_0' = 'A_0').
tff('declare_C_0',type,'C_0':'Token_0()').
tff('C_0_definition',axiom,'C_0' = 'A_0').
tff('declare_D_0',type,'D_0':'Token_0()').
tff('D_0_definition',axiom,'D_0' = 'A_0').
tff('declare_Q_0',type,'Q_0':'Token_0()').
tff('Q_0_definition',axiom,'Q_0' = 'P_0').
tff('declare_R_0',type,'R_0':'Token_0()').
tff('R_0_definition',axiom,'R_0' = 'P_0').
tff(declare_cons_0,type,cons_0: 'Token_0()' * 'list_0()' > 'list_0()').
tff(function_cons_0,axiom,
           cons_0('A_0',nil_0) = nil_0
         & cons_0('A_0',fmb_'list_0()'_2) = fmb_'list_0()'_2
         & cons_0('A_0',fmb_'list_0()'_3) = fmb_'list_0()'_3
         & cons_0('ESC_0',nil_0) = nil_0
         & cons_0('ESC_0',fmb_'list_0()'_2) = fmb_'list_0()'_2
         & cons_0('ESC_0',fmb_'list_0()'_3) = fmb_'list_0()'_3
         & cons_0('P_0',nil_0) = fmb_'list_0()'_2
         & cons_0('P_0',fmb_'list_0()'_2) = fmb_'list_0()'_2
         & cons_0('P_0',fmb_'list_0()'_3) = nil_0

).

tff(declare_diseqBool_0,type,diseqBool_0: 'Bool_0()' * 'Bool_0()' > $o ).
tff(predicate_diseqBool_0,axiom,
           diseqBool_0(false_0,false_0)
         & diseqBool_0(false_0,true_0)
%         diseqBool_0(false_0,fmb_'Bool_0()'_3) undefined in model
         & ~diseqBool_0(true_0,false_0)
         & ~diseqBool_0(true_0,true_0)
%         diseqBool_0(true_0,fmb_'Bool_0()'_3) undefined in model
         & ~diseqBool_0(fmb_'Bool_0()'_3,false_0)
         & ~diseqBool_0(fmb_'Bool_0()'_3,true_0)
%         diseqBool_0(fmb_'Bool_0()'_3,fmb_'Bool_0()'_3) undefined in model

).

tff(declare_isfalse_1,type,isfalse_1: 'Bool_0()' > $o ).
tff(predicate_isfalse_1,axiom,
%         isfalse_1(false_0) undefined in model
%         isfalse_1(true_0) undefined in model
%         isfalse_1(fmb_'Bool_0()'_3) undefined in model

).

tff(declare_istrue_1,type,istrue_1: 'Bool_0()' > $o ).
tff(predicate_istrue_1,axiom,
%         istrue_1(false_0) undefined in model
%         istrue_1(true_0) undefined in model
%         istrue_1(fmb_'Bool_0()'_3) undefined in model

).

tff(declare_and_0,type,and_0: 'Bool_0()' * 'Bool_0()' * 'Bool_0()' > $o ).
tff(predicate_and_0,axiom,
           and_0(false_0,false_0,false_0)
         & and_0(false_0,false_0,true_0)
%         and_0(false_0,false_0,fmb_'Bool_0()'_3) undefined in model
         & and_0(false_0,true_0,false_0)
         & ~and_0(false_0,true_0,true_0)
%         and_0(false_0,true_0,fmb_'Bool_0()'_3) undefined in model
%         and_0(false_0,fmb_'Bool_0()'_3,false_0) undefined in model
%         and_0(false_0,fmb_'Bool_0()'_3,true_0) undefined in model
%         and_0(false_0,fmb_'Bool_0()'_3,fmb_'Bool_0()'_3) undefined in model
         & ~and_0(true_0,false_0,false_0)
         & ~and_0(true_0,false_0,true_0)
%         and_0(true_0,false_0,fmb_'Bool_0()'_3) undefined in model
         & ~and_0(true_0,true_0,false_0)
         & and_0(true_0,true_0,true_0)
%         and_0(true_0,true_0,fmb_'Bool_0()'_3) undefined in model
%         and_0(true_0,fmb_'Bool_0()'_3,false_0) undefined in model
%         and_0(true_0,fmb_'Bool_0()'_3,true_0) undefined in model
%         and_0(true_0,fmb_'Bool_0()'_3,fmb_'Bool_0()'_3) undefined in model
         & ~and_0(fmb_'Bool_0()'_3,false_0,false_0)
         & ~and_0(fmb_'Bool_0()'_3,false_0,true_0)
%         and_0(fmb_'Bool_0()'_3,false_0,fmb_'Bool_0()'_3) undefined in model
         & ~and_0(fmb_'Bool_0()'_3,true_0,false_0)
         & ~and_0(fmb_'Bool_0()'_3,true_0,true_0)
%         and_0(fmb_'Bool_0()'_3,true_0,fmb_'Bool_0()'_3) undefined in model
%         and_0(fmb_'Bool_0()'_3,fmb_'Bool_0()'_3,false_0) undefined in model
%         and_0(fmb_'Bool_0()'_3,fmb_'Bool_0()'_3,true_0) undefined in model
%         and_0(fmb_'Bool_0()'_3,fmb_'Bool_0()'_3,fmb_'Bool_0()'_3) undefined in model

).

tff(declare_or_0,type,or_0: 'Bool_0()' * 'Bool_0()' * 'Bool_0()' > $o ).
tff(predicate_or_0,axiom,
%         or_0(false_0,false_0,false_0) undefined in model
%         or_0(false_0,false_0,true_0) undefined in model
%         or_0(false_0,false_0,fmb_'Bool_0()'_3) undefined in model
%         or_0(false_0,true_0,false_0) undefined in model
%         or_0(false_0,true_0,true_0) undefined in model
%         or_0(false_0,true_0,fmb_'Bool_0()'_3) undefined in model
%         or_0(false_0,fmb_'Bool_0()'_3,false_0) undefined in model
%         or_0(false_0,fmb_'Bool_0()'_3,true_0) undefined in model
%         or_0(false_0,fmb_'Bool_0()'_3,fmb_'Bool_0()'_3) undefined in model
%         or_0(true_0,false_0,false_0) undefined in model
%         or_0(true_0,false_0,true_0) undefined in model
%         or_0(true_0,false_0,fmb_'Bool_0()'_3) undefined in model
%         or_0(true_0,true_0,false_0) undefined in model
%         or_0(true_0,true_0,true_0) undefined in model
%         or_0(true_0,true_0,fmb_'Bool_0()'_3) undefined in model
%         or_0(true_0,fmb_'Bool_0()'_3,false_0) undefined in model
%         or_0(true_0,fmb_'Bool_0()'_3,true_0) undefined in model
%         or_0(true_0,fmb_'Bool_0()'_3,fmb_'Bool_0()'_3) undefined in model
%         or_0(fmb_'Bool_0()'_3,false_0,false_0) undefined in model
%         or_0(fmb_'Bool_0()'_3,false_0,true_0) undefined in model
%         or_0(fmb_'Bool_0()'_3,false_0,fmb_'Bool_0()'_3) undefined in model
%         or_0(fmb_'Bool_0()'_3,true_0,false_0) undefined in model
%         or_0(fmb_'Bool_0()'_3,true_0,true_0) undefined in model
%         or_0(fmb_'Bool_0()'_3,true_0,fmb_'Bool_0()'_3) undefined in model
%         or_0(fmb_'Bool_0()'_3,fmb_'Bool_0()'_3,false_0) undefined in model
%         or_0(fmb_'Bool_0()'_3,fmb_'Bool_0()'_3,true_0) undefined in model
%         or_0(fmb_'Bool_0()'_3,fmb_'Bool_0()'_3,fmb_'Bool_0()'_3) undefined in model

).

tff(declare_hence_0,type,hence_0: 'Bool_0()' * 'Bool_0()' * 'Bool_0()' > $o ).
tff(predicate_hence_0,axiom,
%         hence_0(false_0,false_0,false_0) undefined in model
%         hence_0(false_0,false_0,true_0) undefined in model
%         hence_0(false_0,false_0,fmb_'Bool_0()'_3) undefined in model
%         hence_0(false_0,true_0,false_0) undefined in model
%         hence_0(false_0,true_0,true_0) undefined in model
%         hence_0(false_0,true_0,fmb_'Bool_0()'_3) undefined in model
%         hence_0(false_0,fmb_'Bool_0()'_3,false_0) undefined in model
%         hence_0(false_0,fmb_'Bool_0()'_3,true_0) undefined in model
%         hence_0(false_0,fmb_'Bool_0()'_3,fmb_'Bool_0()'_3) undefined in model
%         hence_0(true_0,false_0,false_0) undefined in model
%         hence_0(true_0,false_0,true_0) undefined in model
%         hence_0(true_0,false_0,fmb_'Bool_0()'_3) undefined in model
%         hence_0(true_0,true_0,false_0) undefined in model
%         hence_0(true_0,true_0,true_0) undefined in model
%         hence_0(true_0,true_0,fmb_'Bool_0()'_3) undefined in model
%         hence_0(true_0,fmb_'Bool_0()'_3,false_0) undefined in model
%         hence_0(true_0,fmb_'Bool_0()'_3,true_0) undefined in model
%         hence_0(true_0,fmb_'Bool_0()'_3,fmb_'Bool_0()'_3) undefined in model
%         hence_0(fmb_'Bool_0()'_3,false_0,false_0) undefined in model
%         hence_0(fmb_'Bool_0()'_3,false_0,true_0) undefined in model
%         hence_0(fmb_'Bool_0()'_3,false_0,fmb_'Bool_0()'_3) undefined in model
%         hence_0(fmb_'Bool_0()'_3,true_0,false_0) undefined in model
%         hence_0(fmb_'Bool_0()'_3,true_0,true_0) undefined in model
%         hence_0(fmb_'Bool_0()'_3,true_0,fmb_'Bool_0()'_3) undefined in model
%         hence_0(fmb_'Bool_0()'_3,fmb_'Bool_0()'_3,false_0) undefined in model
%         hence_0(fmb_'Bool_0()'_3,fmb_'Bool_0()'_3,true_0) undefined in model
%         hence_0(fmb_'Bool_0()'_3,fmb_'Bool_0()'_3,fmb_'Bool_0()'_3) undefined in model

).

tff(declare_not_0,type,not_0: 'Bool_0()' * 'Bool_0()' > $o ).
tff(predicate_not_0,axiom,
           ~not_0(false_0,false_0)
         & not_0(false_0,true_0)
%         not_0(false_0,fmb_'Bool_0()'_3) undefined in model
         & not_0(true_0,false_0)
         & ~not_0(true_0,true_0)
%         not_0(true_0,fmb_'Bool_0()'_3) undefined in model
%         not_0(fmb_'Bool_0()'_3,false_0) undefined in model
%         not_0(fmb_'Bool_0()'_3,true_0) undefined in model
%         not_0(fmb_'Bool_0()'_3,fmb_'Bool_0()'_3) undefined in model

).

tff(declare_diseqToken_0,type,diseqToken_0: 'Token_0()' * 'Token_0()' > $o ).
tff(predicate_diseqToken_0,axiom,
           ~diseqToken_0('A_0','A_0')
%         diseqToken_0('A_0','ESC_0') undefined in model
%         diseqToken_0('A_0','P_0') undefined in model
%         diseqToken_0('ESC_0','A_0') undefined in model
%         diseqToken_0('ESC_0','ESC_0') undefined in model
%         diseqToken_0('ESC_0','P_0') undefined in model
%         diseqToken_0('P_0','A_0') undefined in model
%         diseqToken_0('P_0','ESC_0') undefined in model
%         diseqToken_0('P_0','P_0') undefined in model

).

tff(declare_isA_0,type,isA_0: 'Token_0()' > $o ).
tff(predicate_isA_0,axiom,
%         isA_0('A_0') undefined in model
%         isA_0('ESC_0') undefined in model
%         isA_0('P_0') undefined in model

).

tff(declare_isB_0,type,isB_0: 'Token_0()' > $o ).
tff(predicate_isB_0,axiom,
%         isB_0('A_0') undefined in model
%         isB_0('ESC_0') undefined in model
%         isB_0('P_0') undefined in model

).

tff(declare_isC_0,type,isC_0: 'Token_0()' > $o ).
tff(predicate_isC_0,axiom,
%         isC_0('A_0') undefined in model
%         isC_0('ESC_0') undefined in model
%         isC_0('P_0') undefined in model

).

tff(declare_isD_0,type,isD_0: 'Token_0()' > $o ).
tff(predicate_isD_0,axiom,
%         isD_0('A_0') undefined in model
%         isD_0('ESC_0') undefined in model
%         isD_0('P_0') undefined in model

).

tff(declare_isESC_0,type,isESC_0: 'Token_0()' > $o ).
tff(predicate_isESC_0,axiom,
%         isESC_0('A_0') undefined in model
%         isESC_0('ESC_0') undefined in model
%         isESC_0('P_0') undefined in model

).

tff(declare_isP_0,type,isP_0: 'Token_0()' > $o ).
tff(predicate_isP_0,axiom,
%         isP_0('A_0') undefined in model
%         isP_0('ESC_0') undefined in model
%         isP_0('P_0') undefined in model

).

tff(declare_isQ_0,type,isQ_0: 'Token_0()' > $o ).
tff(predicate_isQ_0,axiom,
%         isQ_0('A_0') undefined in model
%         isQ_0('ESC_0') undefined in model
%         isQ_0('P_0') undefined in model

).

tff(declare_isR_0,type,isR_0: 'Token_0()' > $o ).
tff(predicate_isR_0,axiom,
%         isR_0('A_0') undefined in model
%         isR_0('ESC_0') undefined in model
%         isR_0('P_0') undefined in model

).

tff(declare_diseqlist_0,type,diseqlist_0: 'list_0()' * 'list_0()' > $o ).
tff(predicate_diseqlist_0,axiom,
           ~diseqlist_0(nil_0,nil_0)
%         diseqlist_0(nil_0,fmb_'list_0()'_2) undefined in model
%         diseqlist_0(nil_0,fmb_'list_0()'_3) undefined in model
%         diseqlist_0(fmb_'list_0()'_2,nil_0) undefined in model
%         diseqlist_0(fmb_'list_0()'_2,fmb_'list_0()'_2) undefined in model
%         diseqlist_0(fmb_'list_0()'_2,fmb_'list_0()'_3) undefined in model
%         diseqlist_0(fmb_'list_0()'_3,nil_0) undefined in model
%         diseqlist_0(fmb_'list_0()'_3,fmb_'list_0()'_2) undefined in model
%         diseqlist_0(fmb_'list_0()'_3,fmb_'list_0()'_3) undefined in model

).

tff(declare_head_1,type,head_1: 'Token_0()' * 'list_0()' > $o ).
tff(predicate_head_1,axiom,
%         head_1('A_0',nil_0) undefined in model
%         head_1('A_0',fmb_'list_0()'_2) undefined in model
%         head_1('A_0',fmb_'list_0()'_3) undefined in model
%         head_1('ESC_0',nil_0) undefined in model
%         head_1('ESC_0',fmb_'list_0()'_2) undefined in model
%         head_1('ESC_0',fmb_'list_0()'_3) undefined in model
%         head_1('P_0',nil_0) undefined in model
%         head_1('P_0',fmb_'list_0()'_2) undefined in model
%         head_1('P_0',fmb_'list_0()'_3) undefined in model

).

tff(declare_tail_1,type,tail_1: 'list_0()' * 'list_0()' > $o ).
tff(predicate_tail_1,axiom,
%         tail_1(nil_0,nil_0) undefined in model
%         tail_1(nil_0,fmb_'list_0()'_2) undefined in model
%         tail_1(nil_0,fmb_'list_0()'_3) undefined in model
%         tail_1(fmb_'list_0()'_2,nil_0) undefined in model
%         tail_1(fmb_'list_0()'_2,fmb_'list_0()'_2) undefined in model
%         tail_1(fmb_'list_0()'_2,fmb_'list_0()'_3) undefined in model
%         tail_1(fmb_'list_0()'_3,nil_0) undefined in model
%         tail_1(fmb_'list_0()'_3,fmb_'list_0()'_2) undefined in model
%         tail_1(fmb_'list_0()'_3,fmb_'list_0()'_3) undefined in model

).

tff(declare_isnil_0,type,isnil_0: 'list_0()' > $o ).
tff(predicate_isnil_0,axiom,
%         isnil_0(nil_0) undefined in model
%         isnil_0(fmb_'list_0()'_2) undefined in model
%         isnil_0(fmb_'list_0()'_3) undefined in model

).

tff(declare_iscons_0,type,iscons_0: 'list_0()' > $o ).
tff(predicate_iscons_0,axiom,
%         iscons_0(nil_0) undefined in model
%         iscons_0(fmb_'list_0()'_2) undefined in model
%         iscons_0(fmb_'list_0()'_3) undefined in model

).

tff(declare_isSpecial_0,type,isSpecial_0: 'Bool_0()' * 'Token_0()' > $o ).
tff(predicate_isSpecial_0,axiom,
           isSpecial_0(false_0,'A_0')
         & ~isSpecial_0(false_0,'ESC_0')
         & ~isSpecial_0(false_0,'P_0')
         & ~isSpecial_0(true_0,'A_0')
         & isSpecial_0(true_0,'ESC_0')
         & isSpecial_0(true_0,'P_0')
%         isSpecial_0(fmb_'Bool_0()'_3,'A_0') undefined in model
%         isSpecial_0(fmb_'Bool_0()'_3,'ESC_0') undefined in model
%         isSpecial_0(fmb_'Bool_0()'_3,'P_0') undefined in model

).

tff(declare_ok_0,type,ok_0: 'Bool_0()' * 'Token_0()' > $o ).
tff(predicate_ok_0,axiom,
           ~ok_0(false_0,'A_0')
         & ~ok_0(false_0,'ESC_0')
         & ok_0(false_0,'P_0')
         & ok_0(true_0,'A_0')
         & ok_0(true_0,'ESC_0')
         & ~ok_0(true_0,'P_0')
%         ok_0(fmb_'Bool_0()'_3,'A_0') undefined in model
%         ok_0(fmb_'Bool_0()'_3,'ESC_0') undefined in model
%         ok_0(fmb_'Bool_0()'_3,'P_0') undefined in model

).

tff(declare_formula_0,type,formula_0: 'Bool_0()' * 'list_0()' > $o ).
tff(predicate_formula_0,axiom,
           ~formula_0(false_0,nil_0)
         & formula_0(false_0,fmb_'list_0()'_2)
         & ~formula_0(false_0,fmb_'list_0()'_3)
         & formula_0(true_0,nil_0)
         & formula_0(true_0,fmb_'list_0()'_2)
         & ~formula_0(true_0,fmb_'list_0()'_3)
%         formula_0(fmb_'Bool_0()'_3,nil_0) undefined in model
%         formula_0(fmb_'Bool_0()'_3,fmb_'list_0()'_2) undefined in model
%         formula_0(fmb_'Bool_0()'_3,fmb_'list_0()'_3) undefined in model

).

tff(declare_code_0,type,code_0: 'Token_0()' * 'Token_0()' > $o ).
tff(predicate_code_0,axiom,
           code_0('A_0','A_0')
         & code_0('A_0','ESC_0')
         & code_0('A_0','P_0')
         & ~code_0('ESC_0','A_0')
         & code_0('ESC_0','ESC_0')
         & ~code_0('ESC_0','P_0')
         & ~code_0('P_0','A_0')
         & ~code_0('P_0','ESC_0')
         & ~code_0('P_0','P_0')

).

tff(declare_escape_0,type,escape_0: 'list_0()' * 'list_0()' > $o ).
tff(predicate_escape_0,axiom,
           escape_0(nil_0,nil_0)
         & escape_0(nil_0,fmb_'list_0()'_2)
         & escape_0(nil_0,fmb_'list_0()'_3)
         & ~escape_0(fmb_'list_0()'_2,nil_0)
         & ~escape_0(fmb_'list_0()'_2,fmb_'list_0()'_2)
         & ~escape_0(fmb_'list_0()'_2,fmb_'list_0()'_3)
         & ~escape_0(fmb_'list_0()'_3,nil_0)
         & ~escape_0(fmb_'list_0()'_3,fmb_'list_0()'_2)
         & ~escape_0(fmb_'list_0()'_3,fmb_'list_0()'_3)

).

% SZS output end FiniteModel for escape_NoSpecial
% ------------------------------
% Version: Vampire 4.6.1 (commit af1735c99 on 2021-12-01 14:43:47 +0100)
