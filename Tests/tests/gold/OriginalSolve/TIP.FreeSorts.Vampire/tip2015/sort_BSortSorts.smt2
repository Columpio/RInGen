9
35448
870
UNKNOWN % Warning: check-sat is not the last entry. Skipping the rest!
% ott+10_128_av=off:bs=on:gsp=input_only:irw=on:lcm=predicate:lma=on:nm=0:nwc=1:sp=occurrence:urr=on:updr=off:uhcvi=on_4 on sort_BSortSorts
% Time limit reached!
% ------------------------------
% Version: Vampire 4.6.1 (commit af1735c99 on 2021-12-01 14:43:47 +0100)
% Linked with Z3 4.8.13.0 f03d756e086f81f2596157241e0decfb1c982299 z3-4.8.4-5390-gf03d756e0
% Termination reason: Time limit
% Termination phase: Saturation

% Memory used [KB]: 25585
% Time elapsed: 0.800 s
% ------------------------------
% ------------------------------
% fmb+10_1_av=off:bce=on:nm=6_1461 on sort_BSortSorts
TRYING [1]
TRYING [2]
TRYING [3]
Finite Model Found!
% SZS status Satisfiable for sort_BSortSorts
% SZS output start FiniteModel for sort_BSortSorts
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

tff('declare_Nat_0()',type,'Nat_0()':$tType).
tff('declare_Nat_0()1',type,'Z_6':'Nat_0()').
tff('declare_Nat_0()2',type,fmb_'Nat_0()'_2:'Nat_0()').
tff('declare_Nat_0()3',type,fmb_'Nat_0()'_3:'Nat_0()').
tff(finite_domain,axiom,
      ! [X:'Nat_0()'] : (
         X = 'Z_6' | X = fmb_'Nat_0()'_2 | X = fmb_'Nat_0()'_3
      ) ).

tff(distinct_domain,axiom,
         'Z_6' != fmb_'Nat_0()'_2 & 'Z_6' != fmb_'Nat_0()'_3 & fmb_'Nat_0()'_2 != fmb_'Nat_0()'_3
).

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

tff('declare_Z_7',type,'Z_7': 'Nat_0()' > 'Nat_0()').
tff('function_Z_7',axiom,
           'Z_7'('Z_6') = fmb_'Nat_0()'_2
         & 'Z_7'(fmb_'Nat_0()'_2) = fmb_'Nat_0()'_2
         & 'Z_7'(fmb_'Nat_0()'_3) = fmb_'Nat_0()'_2

).

tff(declare_cons_0,type,cons_0: 'Nat_0()' * 'list_0()' > 'list_0()').
tff(function_cons_0,axiom,
           cons_0('Z_6',nil_0) = fmb_'list_0()'_2
         & cons_0('Z_6',fmb_'list_0()'_2) = fmb_'list_0()'_3
         & cons_0('Z_6',fmb_'list_0()'_3) = fmb_'list_0()'_3
         & cons_0(fmb_'Nat_0()'_2,nil_0) = fmb_'list_0()'_2
         & cons_0(fmb_'Nat_0()'_2,fmb_'list_0()'_2) = fmb_'list_0()'_3
         & cons_0(fmb_'Nat_0()'_2,fmb_'list_0()'_3) = fmb_'list_0()'_3
         & cons_0(fmb_'Nat_0()'_3,nil_0) = nil_0
         & cons_0(fmb_'Nat_0()'_3,fmb_'list_0()'_2) = fmb_'list_0()'_3
         & cons_0(fmb_'Nat_0()'_3,fmb_'list_0()'_3) = fmb_'list_0()'_3

).

tff(declare_diseqNat_0,type,diseqNat_0: 'Nat_0()' * 'Nat_0()' > $o ).
tff(predicate_diseqNat_0,axiom,
           ~diseqNat_0('Z_6','Z_6')
%         diseqNat_0('Z_6',fmb_'Nat_0()'_2) undefined in model
%         diseqNat_0('Z_6',fmb_'Nat_0()'_3) undefined in model
         & ~diseqNat_0(fmb_'Nat_0()'_2,'Z_6')
%         diseqNat_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         diseqNat_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         diseqNat_0(fmb_'Nat_0()'_3,'Z_6') undefined in model
%         diseqNat_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         diseqNat_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model

).

tff(declare_unS_1,type,unS_1: 'Nat_0()' * 'Nat_0()' > $o ).
tff(predicate_unS_1,axiom,
%         unS_1('Z_6','Z_6') undefined in model
%         unS_1('Z_6',fmb_'Nat_0()'_2) undefined in model
%         unS_1('Z_6',fmb_'Nat_0()'_3) undefined in model
%         unS_1(fmb_'Nat_0()'_2,'Z_6') undefined in model
%         unS_1(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         unS_1(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         unS_1(fmb_'Nat_0()'_3,'Z_6') undefined in model
%         unS_1(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         unS_1(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model

).

tff(declare_isZ_2,type,isZ_2: 'Nat_0()' > $o ).
tff(predicate_isZ_2,axiom,
%         isZ_2('Z_6') undefined in model
%         isZ_2(fmb_'Nat_0()'_2) undefined in model
%         isZ_2(fmb_'Nat_0()'_3) undefined in model

).

tff(declare_isZ_3,type,isZ_3: 'Nat_0()' > $o ).
tff(predicate_isZ_3,axiom,
%         isZ_3('Z_6') undefined in model
%         isZ_3(fmb_'Nat_0()'_2) undefined in model
%         isZ_3(fmb_'Nat_0()'_3) undefined in model

).

tff(declare_add_0,type,add_0: 'Nat_0()' * 'Nat_0()' * 'Nat_0()' > $o ).
tff(predicate_add_0,axiom,
           ~add_0('Z_6','Z_6','Z_6')
%         add_0('Z_6','Z_6',fmb_'Nat_0()'_2) undefined in model
%         add_0('Z_6','Z_6',fmb_'Nat_0()'_3) undefined in model
%         add_0('Z_6',fmb_'Nat_0()'_2,'Z_6') undefined in model
%         add_0('Z_6',fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         add_0('Z_6',fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         add_0('Z_6',fmb_'Nat_0()'_3,'Z_6') undefined in model
%         add_0('Z_6',fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         add_0('Z_6',fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model
         & ~add_0(fmb_'Nat_0()'_2,'Z_6','Z_6')
%         add_0(fmb_'Nat_0()'_2,'Z_6',fmb_'Nat_0()'_2) undefined in model
%         add_0(fmb_'Nat_0()'_2,'Z_6',fmb_'Nat_0()'_3) undefined in model
%         add_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,'Z_6') undefined in model
%         add_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         add_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         add_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,'Z_6') undefined in model
%         add_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         add_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model
%         add_0(fmb_'Nat_0()'_3,'Z_6','Z_6') undefined in model
%         add_0(fmb_'Nat_0()'_3,'Z_6',fmb_'Nat_0()'_2) undefined in model
%         add_0(fmb_'Nat_0()'_3,'Z_6',fmb_'Nat_0()'_3) undefined in model
%         add_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,'Z_6') undefined in model
%         add_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         add_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         add_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,'Z_6') undefined in model
%         add_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         add_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model

).

tff(declare_minus_0,type,minus_0: 'Nat_0()' * 'Nat_0()' * 'Nat_0()' > $o ).
tff(predicate_minus_0,axiom,
           ~minus_0('Z_6','Z_6','Z_6')
%         minus_0('Z_6','Z_6',fmb_'Nat_0()'_2) undefined in model
%         minus_0('Z_6','Z_6',fmb_'Nat_0()'_3) undefined in model
%         minus_0('Z_6',fmb_'Nat_0()'_2,'Z_6') undefined in model
%         minus_0('Z_6',fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         minus_0('Z_6',fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         minus_0('Z_6',fmb_'Nat_0()'_3,'Z_6') undefined in model
%         minus_0('Z_6',fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         minus_0('Z_6',fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model
%         minus_0(fmb_'Nat_0()'_2,'Z_6','Z_6') undefined in model
%         minus_0(fmb_'Nat_0()'_2,'Z_6',fmb_'Nat_0()'_2) undefined in model
%         minus_0(fmb_'Nat_0()'_2,'Z_6',fmb_'Nat_0()'_3) undefined in model
%         minus_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,'Z_6') undefined in model
%         minus_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         minus_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         minus_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,'Z_6') undefined in model
%         minus_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         minus_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model
%         minus_0(fmb_'Nat_0()'_3,'Z_6','Z_6') undefined in model
%         minus_0(fmb_'Nat_0()'_3,'Z_6',fmb_'Nat_0()'_2) undefined in model
%         minus_0(fmb_'Nat_0()'_3,'Z_6',fmb_'Nat_0()'_3) undefined in model
%         minus_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,'Z_6') undefined in model
%         minus_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         minus_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         minus_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,'Z_6') undefined in model
%         minus_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         minus_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model

).

tff(declare_le_0,type,le_0: 'Nat_0()' * 'Nat_0()' > $o ).
tff(predicate_le_0,axiom,
           le_0('Z_6','Z_6')
         & le_0('Z_6',fmb_'Nat_0()'_2)
         & le_0('Z_6',fmb_'Nat_0()'_3)
         & ~le_0(fmb_'Nat_0()'_2,'Z_6')
         & le_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2)
         & le_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3)
         & ~le_0(fmb_'Nat_0()'_3,'Z_6')
         & ~le_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2)
         & ~le_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3)

).

tff(declare_ge_0,type,ge_0: 'Nat_0()' * 'Nat_0()' > $o ).
tff(predicate_ge_0,axiom,
           ~ge_0('Z_6','Z_6')
%         ge_0('Z_6',fmb_'Nat_0()'_2) undefined in model
%         ge_0('Z_6',fmb_'Nat_0()'_3) undefined in model
%         ge_0(fmb_'Nat_0()'_2,'Z_6') undefined in model
%         ge_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         ge_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         ge_0(fmb_'Nat_0()'_3,'Z_6') undefined in model
%         ge_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         ge_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model

).

tff(declare_lt_0,type,lt_0: 'Nat_0()' * 'Nat_0()' > $o ).
tff(predicate_lt_0,axiom,
           ~lt_0('Z_6','Z_6')
%         lt_0('Z_6',fmb_'Nat_0()'_2) undefined in model
%         lt_0('Z_6',fmb_'Nat_0()'_3) undefined in model
%         lt_0(fmb_'Nat_0()'_2,'Z_6') undefined in model
%         lt_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         lt_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         lt_0(fmb_'Nat_0()'_3,'Z_6') undefined in model
%         lt_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         lt_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model

).

tff(declare_gt_0,type,gt_0: 'Nat_0()' * 'Nat_0()' > $o ).
tff(predicate_gt_0,axiom,
           ~gt_0('Z_6','Z_6')
         & ~gt_0('Z_6',fmb_'Nat_0()'_2)
         & ~gt_0('Z_6',fmb_'Nat_0()'_3)
         & gt_0(fmb_'Nat_0()'_2,'Z_6')
         & gt_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2)
         & ~gt_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3)
         & gt_0(fmb_'Nat_0()'_3,'Z_6')
         & gt_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2)
         & ~gt_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3)

).

tff(declare_mult_0,type,mult_0: 'Nat_0()' * 'Nat_0()' * 'Nat_0()' > $o ).
tff(predicate_mult_0,axiom,
           ~mult_0('Z_6','Z_6','Z_6')
%         mult_0('Z_6','Z_6',fmb_'Nat_0()'_2) undefined in model
%         mult_0('Z_6','Z_6',fmb_'Nat_0()'_3) undefined in model
%         mult_0('Z_6',fmb_'Nat_0()'_2,'Z_6') undefined in model
%         mult_0('Z_6',fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         mult_0('Z_6',fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         mult_0('Z_6',fmb_'Nat_0()'_3,'Z_6') undefined in model
%         mult_0('Z_6',fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         mult_0('Z_6',fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model
%         mult_0(fmb_'Nat_0()'_2,'Z_6','Z_6') undefined in model
%         mult_0(fmb_'Nat_0()'_2,'Z_6',fmb_'Nat_0()'_2) undefined in model
%         mult_0(fmb_'Nat_0()'_2,'Z_6',fmb_'Nat_0()'_3) undefined in model
%         mult_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,'Z_6') undefined in model
%         mult_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         mult_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         mult_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,'Z_6') undefined in model
%         mult_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         mult_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model
%         mult_0(fmb_'Nat_0()'_3,'Z_6','Z_6') undefined in model
%         mult_0(fmb_'Nat_0()'_3,'Z_6',fmb_'Nat_0()'_2) undefined in model
%         mult_0(fmb_'Nat_0()'_3,'Z_6',fmb_'Nat_0()'_3) undefined in model
%         mult_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,'Z_6') undefined in model
%         mult_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         mult_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         mult_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,'Z_6') undefined in model
%         mult_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         mult_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model

).

tff(declare_div_0,type,div_0: 'Nat_0()' * 'Nat_0()' * 'Nat_0()' > $o ).
tff(predicate_div_0,axiom,
           ~div_0('Z_6','Z_6','Z_6')
%         div_0('Z_6','Z_6',fmb_'Nat_0()'_2) undefined in model
%         div_0('Z_6','Z_6',fmb_'Nat_0()'_3) undefined in model
%         div_0('Z_6',fmb_'Nat_0()'_2,'Z_6') undefined in model
%         div_0('Z_6',fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         div_0('Z_6',fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         div_0('Z_6',fmb_'Nat_0()'_3,'Z_6') undefined in model
%         div_0('Z_6',fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         div_0('Z_6',fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model
%         div_0(fmb_'Nat_0()'_2,'Z_6','Z_6') undefined in model
%         div_0(fmb_'Nat_0()'_2,'Z_6',fmb_'Nat_0()'_2) undefined in model
%         div_0(fmb_'Nat_0()'_2,'Z_6',fmb_'Nat_0()'_3) undefined in model
%         div_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,'Z_6') undefined in model
%         div_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         div_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         div_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,'Z_6') undefined in model
%         div_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         div_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model
%         div_0(fmb_'Nat_0()'_3,'Z_6','Z_6') undefined in model
%         div_0(fmb_'Nat_0()'_3,'Z_6',fmb_'Nat_0()'_2) undefined in model
%         div_0(fmb_'Nat_0()'_3,'Z_6',fmb_'Nat_0()'_3) undefined in model
%         div_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,'Z_6') undefined in model
%         div_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         div_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         div_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,'Z_6') undefined in model
%         div_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         div_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model

).

tff(declare_mod_0,type,mod_0: 'Nat_0()' * 'Nat_0()' * 'Nat_0()' > $o ).
tff(predicate_mod_0,axiom,
           ~mod_0('Z_6','Z_6','Z_6')
%         mod_0('Z_6','Z_6',fmb_'Nat_0()'_2) undefined in model
%         mod_0('Z_6','Z_6',fmb_'Nat_0()'_3) undefined in model
%         mod_0('Z_6',fmb_'Nat_0()'_2,'Z_6') undefined in model
%         mod_0('Z_6',fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         mod_0('Z_6',fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         mod_0('Z_6',fmb_'Nat_0()'_3,'Z_6') undefined in model
%         mod_0('Z_6',fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         mod_0('Z_6',fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model
%         mod_0(fmb_'Nat_0()'_2,'Z_6','Z_6') undefined in model
%         mod_0(fmb_'Nat_0()'_2,'Z_6',fmb_'Nat_0()'_2) undefined in model
%         mod_0(fmb_'Nat_0()'_2,'Z_6',fmb_'Nat_0()'_3) undefined in model
%         mod_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,'Z_6') undefined in model
%         mod_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         mod_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         mod_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,'Z_6') undefined in model
%         mod_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         mod_0(fmb_'Nat_0()'_2,fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model
%         mod_0(fmb_'Nat_0()'_3,'Z_6','Z_6') undefined in model
%         mod_0(fmb_'Nat_0()'_3,'Z_6',fmb_'Nat_0()'_2) undefined in model
%         mod_0(fmb_'Nat_0()'_3,'Z_6',fmb_'Nat_0()'_3) undefined in model
%         mod_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,'Z_6') undefined in model
%         mod_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,fmb_'Nat_0()'_2) undefined in model
%         mod_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_2,fmb_'Nat_0()'_3) undefined in model
%         mod_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,'Z_6') undefined in model
%         mod_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,fmb_'Nat_0()'_2) undefined in model
%         mod_0(fmb_'Nat_0()'_3,fmb_'Nat_0()'_3,fmb_'Nat_0()'_3) undefined in model

).

tff(declare_diseqBool_0,type,diseqBool_0: 'Bool_0()' * 'Bool_0()' > $o ).
tff(predicate_diseqBool_0,axiom,
           diseqBool_0(false_0,false_0)
         & diseqBool_0(false_0,true_0)
%         diseqBool_0(false_0,fmb_'Bool_0()'_3) undefined in model
         & ~diseqBool_0(true_0,false_0)
         & ~diseqBool_0(true_0,true_0)
%         diseqBool_0(true_0,fmb_'Bool_0()'_3) undefined in model
%         diseqBool_0(fmb_'Bool_0()'_3,false_0) undefined in model
%         diseqBool_0(fmb_'Bool_0()'_3,true_0) undefined in model
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
%         and_0(false_0,false_0,false_0) undefined in model
%         and_0(false_0,false_0,true_0) undefined in model
%         and_0(false_0,false_0,fmb_'Bool_0()'_3) undefined in model
%         and_0(false_0,true_0,false_0) undefined in model
%         and_0(false_0,true_0,true_0) undefined in model
%         and_0(false_0,true_0,fmb_'Bool_0()'_3) undefined in model
%         and_0(false_0,fmb_'Bool_0()'_3,false_0) undefined in model
%         and_0(false_0,fmb_'Bool_0()'_3,true_0) undefined in model
%         and_0(false_0,fmb_'Bool_0()'_3,fmb_'Bool_0()'_3) undefined in model
%         and_0(true_0,false_0,false_0) undefined in model
%         and_0(true_0,false_0,true_0) undefined in model
%         and_0(true_0,false_0,fmb_'Bool_0()'_3) undefined in model
%         and_0(true_0,true_0,false_0) undefined in model
%         and_0(true_0,true_0,true_0) undefined in model
%         and_0(true_0,true_0,fmb_'Bool_0()'_3) undefined in model
%         and_0(true_0,fmb_'Bool_0()'_3,false_0) undefined in model
%         and_0(true_0,fmb_'Bool_0()'_3,true_0) undefined in model
%         and_0(true_0,fmb_'Bool_0()'_3,fmb_'Bool_0()'_3) undefined in model
%         and_0(fmb_'Bool_0()'_3,false_0,false_0) undefined in model
%         and_0(fmb_'Bool_0()'_3,false_0,true_0) undefined in model
%         and_0(fmb_'Bool_0()'_3,false_0,fmb_'Bool_0()'_3) undefined in model
%         and_0(fmb_'Bool_0()'_3,true_0,false_0) undefined in model
%         and_0(fmb_'Bool_0()'_3,true_0,true_0) undefined in model
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
%         not_0(false_0,false_0) undefined in model
%         not_0(false_0,true_0) undefined in model
%         not_0(false_0,fmb_'Bool_0()'_3) undefined in model
%         not_0(true_0,false_0) undefined in model
%         not_0(true_0,true_0) undefined in model
%         not_0(true_0,fmb_'Bool_0()'_3) undefined in model
%         not_0(fmb_'Bool_0()'_3,false_0) undefined in model
%         not_0(fmb_'Bool_0()'_3,true_0) undefined in model
%         not_0(fmb_'Bool_0()'_3,fmb_'Bool_0()'_3) undefined in model

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

tff(declare_head_1,type,head_1: 'Nat_0()' * 'list_0()' > $o ).
tff(predicate_head_1,axiom,
%         head_1('Z_6',nil_0) undefined in model
%         head_1('Z_6',fmb_'list_0()'_2) undefined in model
%         head_1('Z_6',fmb_'list_0()'_3) undefined in model
%         head_1(fmb_'Nat_0()'_2,nil_0) undefined in model
%         head_1(fmb_'Nat_0()'_2,fmb_'list_0()'_2) undefined in model
%         head_1(fmb_'Nat_0()'_2,fmb_'list_0()'_3) undefined in model
%         head_1(fmb_'Nat_0()'_3,nil_0) undefined in model
