(set-logic HORN)
(declare-datatypes ((Bool_0 0)) (((false_0 ) (true_0 ))))
(declare-fun diseqBool_0 (Bool_0 Bool_0) Bool)
(declare-fun isfalse_1 (Bool_0) Bool)
(declare-fun istrue_1 (Bool_0) Bool)
(assert (isfalse_1 false_0))
(assert (istrue_1 true_0))
(assert (diseqBool_0 false_0 true_0))
(assert (diseqBool_0 true_0 false_0))
(declare-fun and_0 (Bool_0 Bool_0 Bool_0) Bool)
(declare-fun or_0 (Bool_0 Bool_0 Bool_0) Bool)
(declare-fun hence_0 (Bool_0 Bool_0 Bool_0) Bool)
(declare-fun not_0 (Bool_0 Bool_0) Bool)
(assert (and_0 false_0 false_0 false_0))
(assert (and_0 false_0 true_0 false_0))
(assert (and_0 false_0 false_0 true_0))
(assert (and_0 true_0 true_0 true_0))
(assert (or_0 false_0 false_0 false_0))
(assert (or_0 true_0 true_0 false_0))
(assert (or_0 true_0 false_0 true_0))
(assert (or_0 true_0 true_0 true_0))
(assert (hence_0 true_0 false_0 false_0))
(assert (hence_0 false_0 true_0 false_0))
(assert (hence_0 true_0 false_0 true_0))
(assert (hence_0 true_0 true_0 true_0))
(assert (not_0 true_0 false_0))
(assert (not_0 false_0 true_0))
(declare-datatypes ((A_0 0)) (((X_0 ) (Y_0 ))))
(declare-fun diseqA_0 (A_0 A_0) Bool)
(declare-fun isX_0 (A_0) Bool)
(declare-fun isY_0 (A_0) Bool)
(assert (isX_0 X_0))
(assert (isY_0 Y_0))
(assert (diseqA_0 X_0 Y_0))
(assert (diseqA_0 Y_0 X_0))
(declare-datatypes ((R_0 0)) (((Nil_0 ) (Eps_0 ) (Atom_0 (projAtom_0 A_0)) (Plus_0 (projPlus_0 R_0) (projPlus_1 R_0)) (Seq_0 (projSeq_0 R_0) (projSeq_1 R_0)) (Star_0 (projStar_0 R_0)))))
(declare-fun diseqR_0 (R_0 R_0) Bool)
(declare-fun projAtom_1 (A_0 R_0) Bool)
(declare-fun projPlus_2 (R_0 R_0) Bool)
(declare-fun projPlus_3 (R_0 R_0) Bool)
(declare-fun projSeq_2 (R_0 R_0) Bool)
(declare-fun projSeq_3 (R_0 R_0) Bool)
(declare-fun projStar_1 (R_0 R_0) Bool)
(declare-fun isNil_0 (R_0) Bool)
(declare-fun isEps_0 (R_0) Bool)
(declare-fun isAtom_0 (R_0) Bool)
(declare-fun isPlus_0 (R_0) Bool)
(declare-fun isSeq_0 (R_0) Bool)
(declare-fun isStar_0 (R_0) Bool)
(assert (forall ((x_2088 A_0))
	(projAtom_1 x_2088 (Atom_0 x_2088))))
(assert (forall ((x_2090 R_0) (x_2091 R_0))
	(projPlus_2 x_2090 (Plus_0 x_2090 x_2091))))
(assert (forall ((x_2090 R_0) (x_2091 R_0))
	(projPlus_3 x_2091 (Plus_0 x_2090 x_2091))))
(assert (forall ((x_2093 R_0) (x_2094 R_0))
	(projSeq_2 x_2093 (Seq_0 x_2093 x_2094))))
(assert (forall ((x_2093 R_0) (x_2094 R_0))
	(projSeq_3 x_2094 (Seq_0 x_2093 x_2094))))
(assert (forall ((x_2096 R_0))
	(projStar_1 x_2096 (Star_0 x_2096))))
(assert (isNil_0 Nil_0))
(assert (isEps_0 Eps_0))
(assert (forall ((x_2098 A_0))
	(isAtom_0 (Atom_0 x_2098))))
(assert (forall ((x_2099 R_0) (x_2100 R_0))
	(isPlus_0 (Plus_0 x_2099 x_2100))))
(assert (forall ((x_2101 R_0) (x_2102 R_0))
	(isSeq_0 (Seq_0 x_2101 x_2102))))
(assert (forall ((x_2103 R_0))
	(isStar_0 (Star_0 x_2103))))
(assert (diseqR_0 Nil_0 Eps_0))
(assert (forall ((x_2104 A_0))
	(diseqR_0 Nil_0 (Atom_0 x_2104))))
(assert (forall ((x_2105 R_0) (x_2106 R_0))
	(diseqR_0 Nil_0 (Plus_0 x_2105 x_2106))))
(assert (forall ((x_2107 R_0) (x_2108 R_0))
	(diseqR_0 Nil_0 (Seq_0 x_2107 x_2108))))
(assert (forall ((x_2109 R_0))
	(diseqR_0 Nil_0 (Star_0 x_2109))))
(assert (diseqR_0 Eps_0 Nil_0))
(assert (forall ((x_2110 A_0))
	(diseqR_0 (Atom_0 x_2110) Nil_0)))
(assert (forall ((x_2111 R_0) (x_2112 R_0))
	(diseqR_0 (Plus_0 x_2111 x_2112) Nil_0)))
(assert (forall ((x_2113 R_0) (x_2114 R_0))
	(diseqR_0 (Seq_0 x_2113 x_2114) Nil_0)))
(assert (forall ((x_2115 R_0))
	(diseqR_0 (Star_0 x_2115) Nil_0)))
(assert (forall ((x_2116 A_0))
	(diseqR_0 Eps_0 (Atom_0 x_2116))))
(assert (forall ((x_2117 R_0) (x_2118 R_0))
	(diseqR_0 Eps_0 (Plus_0 x_2117 x_2118))))
(assert (forall ((x_2119 R_0) (x_2120 R_0))
	(diseqR_0 Eps_0 (Seq_0 x_2119 x_2120))))
(assert (forall ((x_2121 R_0))
	(diseqR_0 Eps_0 (Star_0 x_2121))))
(assert (forall ((x_2122 A_0))
	(diseqR_0 (Atom_0 x_2122) Eps_0)))
(assert (forall ((x_2123 R_0) (x_2124 R_0))
	(diseqR_0 (Plus_0 x_2123 x_2124) Eps_0)))
(assert (forall ((x_2125 R_0) (x_2126 R_0))
	(diseqR_0 (Seq_0 x_2125 x_2126) Eps_0)))
(assert (forall ((x_2127 R_0))
	(diseqR_0 (Star_0 x_2127) Eps_0)))
(assert (forall ((x_2128 A_0) (x_2129 R_0) (x_2130 R_0))
	(diseqR_0 (Atom_0 x_2128) (Plus_0 x_2129 x_2130))))
(assert (forall ((x_2131 A_0) (x_2132 R_0) (x_2133 R_0))
	(diseqR_0 (Atom_0 x_2131) (Seq_0 x_2132 x_2133))))
(assert (forall ((x_2134 A_0) (x_2135 R_0))
	(diseqR_0 (Atom_0 x_2134) (Star_0 x_2135))))
(assert (forall ((x_2136 R_0) (x_2137 R_0) (x_2138 A_0))
	(diseqR_0 (Plus_0 x_2136 x_2137) (Atom_0 x_2138))))
(assert (forall ((x_2139 R_0) (x_2140 R_0) (x_2141 A_0))
	(diseqR_0 (Seq_0 x_2139 x_2140) (Atom_0 x_2141))))
(assert (forall ((x_2142 R_0) (x_2143 A_0))
	(diseqR_0 (Star_0 x_2142) (Atom_0 x_2143))))
(assert (forall ((x_2144 R_0) (x_2145 R_0) (x_2146 R_0) (x_2147 R_0))
	(diseqR_0 (Plus_0 x_2144 x_2145) (Seq_0 x_2146 x_2147))))
(assert (forall ((x_2148 R_0) (x_2149 R_0) (x_2150 R_0))
	(diseqR_0 (Plus_0 x_2148 x_2149) (Star_0 x_2150))))
(assert (forall ((x_2151 R_0) (x_2152 R_0) (x_2153 R_0) (x_2154 R_0))
	(diseqR_0 (Seq_0 x_2151 x_2152) (Plus_0 x_2153 x_2154))))
(assert (forall ((x_2155 R_0) (x_2156 R_0) (x_2157 R_0))
	(diseqR_0 (Star_0 x_2155) (Plus_0 x_2156 x_2157))))
(assert (forall ((x_2158 R_0) (x_2159 R_0) (x_2160 R_0))
	(diseqR_0 (Seq_0 x_2158 x_2159) (Star_0 x_2160))))
(assert (forall ((x_2161 R_0) (x_2162 R_0) (x_2163 R_0))
	(diseqR_0 (Star_0 x_2161) (Seq_0 x_2162 x_2163))))
(assert (forall ((x_2164 A_0) (x_2165 A_0))
	(=> (diseqA_0 x_2164 x_2165)
	    (diseqR_0 (Atom_0 x_2164) (Atom_0 x_2165)))))
(assert (forall ((x_2166 R_0) (x_2167 R_0) (x_2168 R_0) (x_2169 R_0))
	(=> (diseqR_0 x_2166 x_2168)
	    (diseqR_0 (Plus_0 x_2166 x_2167) (Plus_0 x_2168 x_2169)))))
(assert (forall ((x_2166 R_0) (x_2167 R_0) (x_2168 R_0) (x_2169 R_0))
	(=> (diseqR_0 x_2167 x_2169)
	    (diseqR_0 (Plus_0 x_2166 x_2167) (Plus_0 x_2168 x_2169)))))
(assert (forall ((x_2170 R_0) (x_2171 R_0) (x_2172 R_0) (x_2173 R_0))
	(=> (diseqR_0 x_2170 x_2172)
	    (diseqR_0 (Seq_0 x_2170 x_2171) (Seq_0 x_2172 x_2173)))))
(assert (forall ((x_2170 R_0) (x_2171 R_0) (x_2172 R_0) (x_2173 R_0))
	(=> (diseqR_0 x_2171 x_2173)
	    (diseqR_0 (Seq_0 x_2170 x_2171) (Seq_0 x_2172 x_2173)))))
(assert (forall ((x_2174 R_0) (x_2175 R_0))
	(=> (diseqR_0 x_2174 x_2175)
	    (diseqR_0 (Star_0 x_2174) (Star_0 x_2175)))))
(declare-datatypes ((list_0 0)) (((nil_1 ) (cons_0 (head_0 A_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (A_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_1 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_2177 A_0) (x_2178 list_0))
	(head_1 x_2177 (cons_0 x_2177 x_2178))))
(assert (forall ((x_2177 A_0) (x_2178 list_0))
	(tail_1 x_2178 (cons_0 x_2177 x_2178))))
(assert (isnil_1 nil_1))
(assert (forall ((x_2180 A_0) (x_2181 list_0))
	(iscons_0 (cons_0 x_2180 x_2181))))
(assert (forall ((x_2182 A_0) (x_2183 list_0))
	(diseqlist_0 nil_1 (cons_0 x_2182 x_2183))))
(assert (forall ((x_2184 A_0) (x_2185 list_0))
	(diseqlist_0 (cons_0 x_2184 x_2185) nil_1)))
(assert (forall ((x_2186 A_0) (x_2187 list_0) (x_2188 A_0) (x_2189 list_0))
	(=> (diseqA_0 x_2186 x_2188)
	    (diseqlist_0 (cons_0 x_2186 x_2187) (cons_0 x_2188 x_2189)))))
(assert (forall ((x_2186 A_0) (x_2187 list_0) (x_2188 A_0) (x_2189 list_0))
	(=> (diseqlist_0 x_2187 x_2189)
	    (diseqlist_0 (cons_0 x_2186 x_2187) (cons_0 x_2188 x_2189)))))
(declare-fun seq_1 (R_0 R_0 R_0) Bool)
(assert (forall ((y_1 R_0))
	(seq_1 Nil_0 Nil_0 y_1)))
(assert (forall ((x_2 R_0) (x_244 A_0))
	(seq_1 Nil_0 (Atom_0 x_244) Nil_0)))
(assert (forall ((x_2 R_0))
	(seq_1 Nil_0 Eps_0 Nil_0)))
(assert (forall ((x_2 R_0) (x_245 R_0) (x_246 R_0))
	(seq_1 Nil_0 (Plus_0 x_245 x_246) Nil_0)))
(assert (forall ((x_2 R_0) (x_247 R_0) (x_248 R_0))
	(seq_1 Nil_0 (Seq_0 x_247 x_248) Nil_0)))
(assert (forall ((x_2 R_0) (x_249 R_0))
	(seq_1 Nil_0 (Star_0 x_249) Nil_0)))
(assert (forall ((x_3 R_0) (x_58 A_0) (x_2 R_0))
	(seq_1 (Atom_0 x_58) Eps_0 (Atom_0 x_58))))
(assert (forall ((x_3 R_0) (x_2 R_0))
	(seq_1 Eps_0 Eps_0 Eps_0)))
(assert (forall ((x_3 R_0) (x_59 R_0) (x_60 R_0) (x_2 R_0))
	(seq_1 (Plus_0 x_59 x_60) Eps_0 (Plus_0 x_59 x_60))))
(assert (forall ((x_3 R_0) (x_61 R_0) (x_62 R_0) (x_2 R_0))
	(seq_1 (Seq_0 x_61 x_62) Eps_0 (Seq_0 x_61 x_62))))
(assert (forall ((x_3 R_0) (x_63 R_0) (x_2 R_0))
	(seq_1 (Star_0 x_63) Eps_0 (Star_0 x_63))))
(assert (forall ((x_4 R_0) (x_22 A_0) (x_3 R_0) (x_2 R_0))
	(seq_1 (Atom_0 x_22) (Atom_0 x_22) Eps_0)))
(assert (forall ((x_4 R_0) (x_23 R_0) (x_24 R_0) (x_3 R_0) (x_2 R_0))
	(seq_1 (Plus_0 x_23 x_24) (Plus_0 x_23 x_24) Eps_0)))
(assert (forall ((x_4 R_0) (x_25 R_0) (x_26 R_0) (x_3 R_0) (x_2 R_0))
	(seq_1 (Seq_0 x_25 x_26) (Seq_0 x_25 x_26) Eps_0)))
(assert (forall ((x_4 R_0) (x_27 R_0) (x_3 R_0) (x_2 R_0))
	(seq_1 (Star_0 x_27) (Star_0 x_27) Eps_0)))
(assert (forall ((x_5 R_0) (x_16 A_0) (x_4 R_0) (x_28 A_0) (x_3 R_0) (x_2 R_0))
	(seq_1 (Seq_0 (Atom_0 x_28) (Atom_0 x_16)) (Atom_0 x_28) (Atom_0 x_16))))
(assert (forall ((x_5 R_0) (x_4 R_0) (x_29 R_0) (x_30 R_0) (x_3 R_0) (x_106 A_0) (x_2 R_0))
	(seq_1 (Seq_0 (Plus_0 x_29 x_30) (Atom_0 x_106)) (Plus_0 x_29 x_30) (Atom_0 x_106))))
(assert (forall ((x_5 R_0) (x_4 R_0) (x_31 R_0) (x_32 R_0) (x_3 R_0) (x_112 A_0) (x_2 R_0))
	(seq_1 (Seq_0 (Seq_0 x_31 x_32) (Atom_0 x_112)) (Seq_0 x_31 x_32) (Atom_0 x_112))))
(assert (forall ((x_5 R_0) (x_4 R_0) (x_33 R_0) (x_3 R_0) (x_118 A_0) (x_2 R_0))
	(seq_1 (Seq_0 (Star_0 x_33) (Atom_0 x_118)) (Star_0 x_33) (Atom_0 x_118))))
(assert (forall ((x_5 R_0) (x_4 R_0) (x_40 A_0) (x_3 R_0) (x_155 R_0) (x_156 R_0) (x_2 R_0))
	(seq_1 (Seq_0 (Atom_0 x_40) (Plus_0 x_155 x_156)) (Atom_0 x_40) (Plus_0 x_155 x_156))))
(assert (forall ((x_5 R_0) (x_4 R_0) (x_41 R_0) (x_42 R_0) (x_3 R_0) (x_167 R_0) (x_168 R_0) (x_2 R_0))
	(seq_1 (Seq_0 (Plus_0 x_41 x_42) (Plus_0 x_167 x_168)) (Plus_0 x_41 x_42) (Plus_0 x_167 x_168))))
(assert (forall ((x_5 R_0) (x_17 R_0) (x_4 R_0) (x_43 R_0) (x_44 R_0) (x_3 R_0) (x_174 R_0) (x_2 R_0))
	(seq_1 (Seq_0 (Seq_0 x_43 x_44) (Plus_0 x_17 x_174)) (Seq_0 x_43 x_44) (Plus_0 x_17 x_174))))
(assert (forall ((x_5 R_0) (x_17 R_0) (x_18 R_0) (x_4 R_0) (x_45 R_0) (x_3 R_0) (x_2 R_0))
	(seq_1 (Seq_0 (Star_0 x_45) (Plus_0 x_17 x_18)) (Star_0 x_45) (Plus_0 x_17 x_18))))
(assert (forall ((x_5 R_0) (x_4 R_0) (x_46 A_0) (x_3 R_0) (x_187 R_0) (x_188 R_0) (x_2 R_0))
	(seq_1 (Seq_0 (Atom_0 x_46) (Seq_0 x_187 x_188)) (Atom_0 x_46) (Seq_0 x_187 x_188))))
(assert (forall ((x_5 R_0) (x_19 R_0) (x_20 R_0) (x_4 R_0) (x_47 R_0) (x_48 R_0) (x_3 R_0) (x_2 R_0))
	(seq_1 (Seq_0 (Plus_0 x_47 x_48) (Seq_0 x_19 x_20)) (Plus_0 x_47 x_48) (Seq_0 x_19 x_20))))
(assert (forall ((x_5 R_0) (x_19 R_0) (x_20 R_0) (x_4 R_0) (x_49 R_0) (x_50 R_0) (x_3 R_0) (x_2 R_0))
	(seq_1 (Seq_0 (Seq_0 x_49 x_50) (Seq_0 x_19 x_20)) (Seq_0 x_49 x_50) (Seq_0 x_19 x_20))))
(assert (forall ((x_5 R_0) (x_19 R_0) (x_20 R_0) (x_4 R_0) (x_3 R_0) (x_2 R_0) (x_1023 R_0))
	(seq_1 (Seq_0 (Star_0 x_1023) (Seq_0 x_19 x_20)) (Star_0 x_1023) (Seq_0 x_19 x_20))))
(assert (forall ((x_5 R_0) (x_21 R_0) (x_4 R_0) (x_3 R_0) (x_2 R_0) (x_1054 A_0))
	(seq_1 (Seq_0 (Atom_0 x_1054) (Star_0 x_21)) (Atom_0 x_1054) (Star_0 x_21))))
(assert (forall ((x_5 R_0) (x_21 R_0) (x_4 R_0) (x_3 R_0) (x_2 R_0) (x_1115 R_0) (x_1116 R_0))
	(seq_1 (Seq_0 (Plus_0 x_1115 x_1116) (Star_0 x_21)) (Plus_0 x_1115 x_1116) (Star_0 x_21))))
(assert (forall ((x_5 R_0) (x_21 R_0) (x_4 R_0) (x_3 R_0) (x_2 R_0) (x_1147 R_0) (x_1148 R_0))
	(seq_1 (Seq_0 (Seq_0 x_1147 x_1148) (Star_0 x_21)) (Seq_0 x_1147 x_1148) (Star_0 x_21))))
(assert (forall ((x_5 R_0) (x_21 R_0) (x_4 R_0) (x_3 R_0) (x_2 R_0) (x_1179 R_0))
	(seq_1 (Seq_0 (Star_0 x_1179) (Star_0 x_21)) (Star_0 x_1179) (Star_0 x_21))))
(declare-fun plus_1 (R_0 R_0 R_0) Bool)
(assert (forall ((x_2004 R_0))
	(plus_1 x_2004 Nil_0 x_2004)))
(assert (forall ((x_7 R_0) (x_1186 A_0))
	(plus_1 (Atom_0 x_1186) (Atom_0 x_1186) Nil_0)))
(assert (forall ((x_7 R_0))
	(plus_1 Eps_0 Eps_0 Nil_0)))
(assert (forall ((x_7 R_0) (x_1187 R_0) (x_1188 R_0))
	(plus_1 (Plus_0 x_1187 x_1188) (Plus_0 x_1187 x_1188) Nil_0)))
(assert (forall ((x_7 R_0) (x_1189 R_0) (x_1190 R_0))
	(plus_1 (Seq_0 x_1189 x_1190) (Seq_0 x_1189 x_1190) Nil_0)))
(assert (forall ((x_7 R_0) (x_1191 R_0))
	(plus_1 (Star_0 x_1191) (Star_0 x_1191) Nil_0)))
(assert (forall ((x_8 R_0) (x_1180 A_0) (x_7 R_0) (x_1192 A_0))
	(plus_1 (Plus_0 (Atom_0 x_1192) (Atom_0 x_1180)) (Atom_0 x_1192) (Atom_0 x_1180))))
(assert (forall ((x_8 R_0) (x_1180 A_0) (x_7 R_0))
	(plus_1 (Plus_0 Eps_0 (Atom_0 x_1180)) Eps_0 (Atom_0 x_1180))))
(assert (forall ((x_8 R_0) (x_1180 A_0) (x_7 R_0) (x_1193 R_0) (x_1194 R_0))
	(plus_1 (Plus_0 (Plus_0 x_1193 x_1194) (Atom_0 x_1180)) (Plus_0 x_1193 x_1194) (Atom_0 x_1180))))
(assert (forall ((x_8 R_0) (x_1180 A_0) (x_7 R_0) (x_1195 R_0) (x_1196 R_0))
	(plus_1 (Plus_0 (Seq_0 x_1195 x_1196) (Atom_0 x_1180)) (Seq_0 x_1195 x_1196) (Atom_0 x_1180))))
(assert (forall ((x_8 R_0) (x_1180 A_0) (x_7 R_0) (x_1197 R_0))
	(plus_1 (Plus_0 (Star_0 x_1197) (Atom_0 x_1180)) (Star_0 x_1197) (Atom_0 x_1180))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_1198 A_0))
	(plus_1 (Plus_0 (Atom_0 x_1198) Eps_0) (Atom_0 x_1198) Eps_0)))
(assert (forall ((x_8 R_0) (x_7 R_0))
	(plus_1 (Plus_0 Eps_0 Eps_0) Eps_0 Eps_0)))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_1199 R_0) (x_1200 R_0))
	(plus_1 (Plus_0 (Plus_0 x_1199 x_1200) Eps_0) (Plus_0 x_1199 x_1200) Eps_0)))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_1201 R_0) (x_1202 R_0))
	(plus_1 (Plus_0 (Seq_0 x_1201 x_1202) Eps_0) (Seq_0 x_1201 x_1202) Eps_0)))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_1203 R_0))
	(plus_1 (Plus_0 (Star_0 x_1203) Eps_0) (Star_0 x_1203) Eps_0)))
(assert (forall ((x_8 R_0) (x_1181 R_0) (x_1182 R_0) (x_7 R_0) (x_1204 A_0))
	(plus_1 (Plus_0 (Atom_0 x_1204) (Plus_0 x_1181 x_1182)) (Atom_0 x_1204) (Plus_0 x_1181 x_1182))))
(assert (forall ((x_8 R_0) (x_1181 R_0) (x_1182 R_0) (x_7 R_0))
	(plus_1 (Plus_0 Eps_0 (Plus_0 x_1181 x_1182)) Eps_0 (Plus_0 x_1181 x_1182))))
(assert (forall ((x_8 R_0) (x_1181 R_0) (x_1182 R_0) (x_7 R_0) (x_1205 R_0) (x_1206 R_0))
	(plus_1 (Plus_0 (Plus_0 x_1205 x_1206) (Plus_0 x_1181 x_1182)) (Plus_0 x_1205 x_1206) (Plus_0 x_1181 x_1182))))
(assert (forall ((x_8 R_0) (x_1181 R_0) (x_1182 R_0) (x_7 R_0) (x_1207 R_0) (x_1208 R_0))
	(plus_1 (Plus_0 (Seq_0 x_1207 x_1208) (Plus_0 x_1181 x_1182)) (Seq_0 x_1207 x_1208) (Plus_0 x_1181 x_1182))))
(assert (forall ((x_8 R_0) (x_1181 R_0) (x_1182 R_0) (x_7 R_0) (x_1209 R_0))
	(plus_1 (Plus_0 (Star_0 x_1209) (Plus_0 x_1181 x_1182)) (Star_0 x_1209) (Plus_0 x_1181 x_1182))))
(assert (forall ((x_8 R_0) (x_1183 R_0) (x_1184 R_0) (x_7 R_0) (x_1210 A_0))
	(plus_1 (Plus_0 (Atom_0 x_1210) (Seq_0 x_1183 x_1184)) (Atom_0 x_1210) (Seq_0 x_1183 x_1184))))
(assert (forall ((x_8 R_0) (x_1183 R_0) (x_1184 R_0) (x_7 R_0))
	(plus_1 (Plus_0 Eps_0 (Seq_0 x_1183 x_1184)) Eps_0 (Seq_0 x_1183 x_1184))))
(assert (forall ((x_8 R_0) (x_1183 R_0) (x_1184 R_0) (x_7 R_0) (x_1211 R_0) (x_1212 R_0))
	(plus_1 (Plus_0 (Plus_0 x_1211 x_1212) (Seq_0 x_1183 x_1184)) (Plus_0 x_1211 x_1212) (Seq_0 x_1183 x_1184))))
(assert (forall ((x_8 R_0) (x_1183 R_0) (x_1184 R_0) (x_7 R_0) (x_1213 R_0) (x_1214 R_0))
	(plus_1 (Plus_0 (Seq_0 x_1213 x_1214) (Seq_0 x_1183 x_1184)) (Seq_0 x_1213 x_1214) (Seq_0 x_1183 x_1184))))
(assert (forall ((x_8 R_0) (x_1183 R_0) (x_1184 R_0) (x_7 R_0) (x_1215 R_0))
	(plus_1 (Plus_0 (Star_0 x_1215) (Seq_0 x_1183 x_1184)) (Star_0 x_1215) (Seq_0 x_1183 x_1184))))
(assert (forall ((x_8 R_0) (x_1185 R_0) (x_7 R_0) (x_1216 A_0))
	(plus_1 (Plus_0 (Atom_0 x_1216) (Star_0 x_1185)) (Atom_0 x_1216) (Star_0 x_1185))))
(assert (forall ((x_8 R_0) (x_1185 R_0) (x_7 R_0))
	(plus_1 (Plus_0 Eps_0 (Star_0 x_1185)) Eps_0 (Star_0 x_1185))))
(assert (forall ((x_8 R_0) (x_1185 R_0) (x_7 R_0) (x_1217 R_0) (x_1218 R_0))
	(plus_1 (Plus_0 (Plus_0 x_1217 x_1218) (Star_0 x_1185)) (Plus_0 x_1217 x_1218) (Star_0 x_1185))))
(assert (forall ((x_8 R_0) (x_1185 R_0) (x_7 R_0) (x_1219 R_0) (x_1220 R_0))
	(plus_1 (Plus_0 (Seq_0 x_1219 x_1220) (Star_0 x_1185)) (Seq_0 x_1219 x_1220) (Star_0 x_1185))))
(assert (forall ((x_8 R_0) (x_1185 R_0) (x_7 R_0) (x_1221 R_0))
	(plus_1 (Plus_0 (Star_0 x_1221) (Star_0 x_1185)) (Star_0 x_1221) (Star_0 x_1185))))
(declare-fun eqA_0 (Bool_0 A_0 A_0) Bool)
(assert (eqA_0 true_0 Y_0 Y_0))
(assert (eqA_0 false_0 Y_0 X_0))
(assert (eqA_0 false_0 X_0 Y_0))
(assert (eqA_0 true_0 X_0 X_0))
(declare-fun eps_1 (Bool_0 R_0) Bool)
(assert (forall ((y_4 R_0))
	(eps_1 true_0 (Star_0 y_4))))
(assert (forall ((x_2040 Bool_0) (x_2041 Bool_0) (x_2042 Bool_0) (r_1 R_0) (q_1 R_0))
	(=>	(and (eps_1 x_2041 r_1)
			(eps_1 x_2042 q_1)
			(and_0 x_2040 x_2041 x_2042))
		(eps_1 x_2040 (Seq_0 r_1 q_1)))))
(assert (forall ((x_2043 Bool_0) (x_2044 Bool_0) (x_2045 Bool_0) (p_0 R_0) (q_0 R_0))
	(=>	(and (eps_1 x_2044 p_0)
			(eps_1 x_2045 q_0)
			(or_0 x_2043 x_2044 x_2045))
		(eps_1 x_2043 (Plus_0 p_0 q_0)))))
(assert (eps_1 true_0 Eps_0))
(assert (forall ((x_11 R_0) (x_1222 A_0))
	(eps_1 false_0 (Atom_0 x_1222))))
(assert (forall ((x_11 R_0))
	(eps_1 false_0 Nil_0)))
(declare-fun epsR_0 (R_0 R_0) Bool)
(assert (forall ((x_12 R_0))
	(=> (eps_1 true_0 x_12)
	    (epsR_0 Eps_0 x_12))))
(assert (forall ((x_2051 Bool_0) (x_12 R_0))
	(=>	(and (diseqBool_0 x_2051 true_0)
			(eps_1 x_2051 x_12))
		(epsR_0 Nil_0 x_12))))
(declare-fun step_0 (R_0 R_0 A_0) Bool)
(assert (forall ((x_2053 R_0) (x_2054 R_0) (p_2 R_0) (y_5 A_0))
	(=>	(and (step_0 x_2054 p_2 y_5)
			(seq_1 x_2053 x_2054 (Star_0 p_2)))
		(step_0 x_2053 (Star_0 p_2) y_5))))
(assert (forall ((x_2056 R_0) (x_2057 R_0) (x_2058 R_0) (x_2059 R_0) (x_2060 R_0) (x_2061 R_0) (r_2 R_0) (q_3 R_0) (y_5 A_0))
	(=>	(and (step_0 x_2057 r_2 y_5)
			(seq_1 x_2058 x_2057 q_3)
			(epsR_0 x_2059 r_2)
			(step_0 x_2060 q_3 y_5)
			(seq_1 x_2061 x_2059 x_2060)
			(plus_1 x_2056 x_2058 x_2061))
		(step_0 x_2056 (Seq_0 r_2 q_3) y_5))))
(assert (forall ((x_2063 R_0) (x_2064 R_0) (x_2065 R_0) (p_1 R_0) (q_2 R_0) (y_5 A_0))
	(=>	(and (step_0 x_2064 p_1 y_5)
			(step_0 x_2065 q_2 y_5)
			(plus_1 x_2063 x_2064 x_2065))
		(step_0 x_2063 (Plus_0 p_1 q_2) y_5))))
(assert (forall ((a_1 A_0) (y_5 A_0))
	(=> (eqA_0 true_0 a_1 y_5)
	    (step_0 Eps_0 (Atom_0 a_1) y_5))))
(assert (forall ((x_2069 Bool_0) (a_1 A_0) (y_5 A_0))
	(=>	(and (diseqBool_0 x_2069 true_0)
			(eqA_0 x_2069 a_1 y_5))
		(step_0 Nil_0 (Atom_0 a_1) y_5))))
(assert (forall ((x_14 R_0) (y_5 A_0))
	(step_0 Nil_0 Eps_0 y_5)))
(assert (forall ((x_14 R_0) (y_5 A_0))
	(step_0 Nil_0 Nil_0 y_5)))
(declare-fun recognise_0 (Bool_0 R_0 list_0) Bool)
(assert (forall ((x_2073 Bool_0) (x_2074 R_0) (z_0 A_0) (xs_0 list_0) (x_15 R_0))
	(=>	(and (step_0 x_2074 x_15 z_0)
			(recognise_0 x_2073 x_2074 xs_0))
		(recognise_0 x_2073 x_15 (cons_0 z_0 xs_0)))))
(assert (forall ((x_2076 Bool_0) (x_15 R_0))
	(=> (eps_1 x_2076 x_15)
	    (recognise_0 x_2076 x_15 nil_1))))
(assert (forall ((s_0 list_0))
	(=> (recognise_0 true_0 Nil_0 s_0)
	    false)))
(check-sat)