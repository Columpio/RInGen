(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_13 ) (Z_14 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_170 Nat_0))
	(unS_1 x_170 (Z_14 x_170))))
(assert (isZ_2 Z_13))
(assert (forall ((x_172 Nat_0))
	(isZ_3 (Z_14 x_172))))
(assert (forall ((x_173 Nat_0))
	(diseqNat_0 Z_13 (Z_14 x_173))))
(assert (forall ((x_174 Nat_0))
	(diseqNat_0 (Z_14 x_174) Z_13)))
(assert (forall ((x_175 Nat_0) (x_176 Nat_0))
	(=> (diseqNat_0 x_175 x_176)
	    (diseqNat_0 (Z_14 x_175) (Z_14 x_176)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_21 Nat_0))
	(add_0 y_21 Z_13 y_21)))
(assert (forall ((r_1 Nat_0) (x_164 Nat_0) (y_21 Nat_0))
	(=> (add_0 r_1 x_164 y_21)
	    (add_0 (Z_14 r_1) (Z_14 x_164) y_21))))
(assert (forall ((y_21 Nat_0))
	(minus_0 Z_13 Z_13 y_21)))
(assert (forall ((r_1 Nat_0) (x_164 Nat_0) (y_21 Nat_0))
	(=> (minus_0 r_1 x_164 y_21)
	    (minus_0 (Z_14 r_1) (Z_14 x_164) y_21))))
(assert (forall ((y_21 Nat_0))
	(le_0 Z_13 y_21)))
(assert (forall ((x_164 Nat_0) (y_21 Nat_0))
	(=> (le_0 x_164 y_21)
	    (le_0 (Z_14 x_164) (Z_14 y_21)))))
(assert (forall ((y_21 Nat_0))
	(ge_0 y_21 Z_13)))
(assert (forall ((x_164 Nat_0) (y_21 Nat_0))
	(=> (ge_0 x_164 y_21)
	    (ge_0 (Z_14 x_164) (Z_14 y_21)))))
(assert (forall ((y_21 Nat_0))
	(lt_0 Z_13 (Z_14 y_21))))
(assert (forall ((x_164 Nat_0) (y_21 Nat_0))
	(=> (lt_0 x_164 y_21)
	    (lt_0 (Z_14 x_164) (Z_14 y_21)))))
(assert (forall ((y_21 Nat_0))
	(gt_0 (Z_14 y_21) Z_13)))
(assert (forall ((x_164 Nat_0) (y_21 Nat_0))
	(=> (gt_0 x_164 y_21)
	    (gt_0 (Z_14 x_164) (Z_14 y_21)))))
(assert (forall ((y_21 Nat_0))
	(mult_0 Z_13 Z_13 y_21)))
(assert (forall ((r_1 Nat_0) (x_164 Nat_0) (y_21 Nat_0) (z_15 Nat_0))
	(=>	(and (mult_0 r_1 x_164 y_21)
			(add_0 z_15 r_1 y_21))
		(mult_0 z_15 (Z_14 x_164) y_21))))
(assert (forall ((x_164 Nat_0) (y_21 Nat_0))
	(=> (lt_0 x_164 y_21)
	    (div_0 Z_13 x_164 y_21))))
(assert (forall ((r_1 Nat_0) (x_164 Nat_0) (y_21 Nat_0) (z_15 Nat_0))
	(=>	(and (ge_0 x_164 y_21)
			(minus_0 z_15 x_164 y_21)
			(div_0 r_1 z_15 y_21))
		(div_0 (Z_14 r_1) x_164 y_21))))
(assert (forall ((x_164 Nat_0) (y_21 Nat_0))
	(=> (lt_0 x_164 y_21)
	    (mod_0 x_164 x_164 y_21))))
(assert (forall ((r_1 Nat_0) (x_164 Nat_0) (y_21 Nat_0) (z_15 Nat_0))
	(=>	(and (ge_0 x_164 y_21)
			(minus_0 z_15 x_164 y_21)
			(mod_0 r_1 z_15 y_21))
		(mod_0 r_1 x_164 y_21))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 Nat_0) (projpair_1 Nat_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_4 (Nat_0 pair_0) Bool)
(declare-fun projpair_5 (Nat_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_177 Nat_0) (x_178 Nat_0))
	(projpair_4 x_177 (pair_1 x_177 x_178))))
(assert (forall ((x_177 Nat_0) (x_178 Nat_0))
	(projpair_5 x_178 (pair_1 x_177 x_178))))
(assert (forall ((x_180 Nat_0) (x_181 Nat_0))
	(ispair_0 (pair_1 x_180 x_181))))
(assert (forall ((x_182 Nat_0) (x_183 Nat_0) (x_184 Nat_0) (x_185 Nat_0))
	(=> (diseqNat_0 x_182 x_184)
	    (diseqpair_0 (pair_1 x_182 x_183) (pair_1 x_184 x_185)))))
(assert (forall ((x_182 Nat_0) (x_183 Nat_0) (x_184 Nat_0) (x_185 Nat_0))
	(=> (diseqNat_0 x_183 x_185)
	    (diseqpair_0 (pair_1 x_182 x_183) (pair_1 x_184 x_185)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_2 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_187 Nat_0) (x_188 list_0))
	(head_1 x_187 (cons_0 x_187 x_188))))
(assert (forall ((x_187 Nat_0) (x_188 list_0))
	(tail_2 x_188 (cons_0 x_187 x_188))))
(assert (isnil_0 nil_0))
(assert (forall ((x_190 Nat_0) (x_191 list_0))
	(iscons_0 (cons_0 x_190 x_191))))
(assert (forall ((x_192 Nat_0) (x_193 list_0))
	(diseqlist_0 nil_0 (cons_0 x_192 x_193))))
(assert (forall ((x_194 Nat_0) (x_195 list_0))
	(diseqlist_0 (cons_0 x_194 x_195) nil_0)))
(assert (forall ((x_196 Nat_0) (x_197 list_0) (x_198 Nat_0) (x_199 list_0))
	(=> (diseqNat_0 x_196 x_198)
	    (diseqlist_0 (cons_0 x_196 x_197) (cons_0 x_198 x_199)))))
(assert (forall ((x_196 Nat_0) (x_197 list_0) (x_198 Nat_0) (x_199 list_0))
	(=> (diseqlist_0 x_197 x_199)
	    (diseqlist_0 (cons_0 x_196 x_197) (cons_0 x_198 x_199)))))
(declare-datatypes ((pair_2 0)) (((pair_3 (projpair_2 list_0) (projpair_3 list_0)))))
(declare-fun diseqpair_1 (pair_2 pair_2) Bool)
(declare-fun projpair_6 (list_0 pair_2) Bool)
(declare-fun projpair_7 (list_0 pair_2) Bool)
(declare-fun ispair_1 (pair_2) Bool)
(assert (forall ((x_200 list_0) (x_201 list_0))
	(projpair_6 x_200 (pair_3 x_200 x_201))))
(assert (forall ((x_200 list_0) (x_201 list_0))
	(projpair_7 x_201 (pair_3 x_200 x_201))))
(assert (forall ((x_203 list_0) (x_204 list_0))
	(ispair_1 (pair_3 x_203 x_204))))
(assert (forall ((x_205 list_0) (x_206 list_0) (x_207 list_0) (x_208 list_0))
	(=> (diseqlist_0 x_205 x_207)
	    (diseqpair_1 (pair_3 x_205 x_206) (pair_3 x_207 x_208)))))
(assert (forall ((x_205 list_0) (x_206 list_0) (x_207 list_0) (x_208 list_0))
	(=> (diseqlist_0 x_206 x_208)
	    (diseqpair_1 (pair_3 x_205 x_206) (pair_3 x_207 x_208)))))
(declare-datatypes ((Q_0 0)) (((Q_1 (projQ_0 list_0) (projQ_1 list_0)))))
(declare-fun diseqQ_0 (Q_0 Q_0) Bool)
(declare-fun projQ_2 (list_0 Q_0) Bool)
(declare-fun projQ_3 (list_0 Q_0) Bool)
(declare-fun isQ_0 (Q_0) Bool)
(assert (forall ((x_209 list_0) (x_210 list_0))
	(projQ_2 x_209 (Q_1 x_209 x_210))))
(assert (forall ((x_209 list_0) (x_210 list_0))
	(projQ_3 x_210 (Q_1 x_209 x_210))))
(assert (forall ((x_212 list_0) (x_213 list_0))
	(isQ_0 (Q_1 x_212 x_213))))
(assert (forall ((x_214 list_0) (x_215 list_0) (x_216 list_0) (x_217 list_0))
	(=> (diseqlist_0 x_214 x_216)
	    (diseqQ_0 (Q_1 x_214 x_215) (Q_1 x_216 x_217)))))
(assert (forall ((x_214 list_0) (x_215 list_0) (x_216 list_0) (x_217 list_0))
	(=> (diseqlist_0 x_215 x_217)
	    (diseqQ_0 (Q_1 x_214 x_215) (Q_1 x_216 x_217)))))
(declare-datatypes ((Maybe_0 0)) (((Nothing_0 ) (Just_0 (projJust_0 Nat_0)))))
(declare-fun diseqMaybe_0 (Maybe_0 Maybe_0) Bool)
(declare-fun projJust_2 (Nat_0 Maybe_0) Bool)
(declare-fun isNothing_0 (Maybe_0) Bool)
(declare-fun isJust_0 (Maybe_0) Bool)
(assert (forall ((x_219 Nat_0))
	(projJust_2 x_219 (Just_0 x_219))))
(assert (isNothing_0 Nothing_0))
(assert (forall ((x_221 Nat_0))
	(isJust_0 (Just_0 x_221))))
(assert (forall ((x_222 Nat_0))
	(diseqMaybe_0 Nothing_0 (Just_0 x_222))))
(assert (forall ((x_223 Nat_0))
	(diseqMaybe_0 (Just_0 x_223) Nothing_0)))
(assert (forall ((x_224 Nat_0) (x_225 Nat_0))
	(=> (diseqNat_0 x_224 x_225)
	    (diseqMaybe_0 (Just_0 x_224) (Just_0 x_225)))))
(declare-datatypes ((Maybe_1 0)) (((Nothing_1 ) (Just_1 (projJust_1 Q_0)))))
(declare-fun diseqMaybe_1 (Maybe_1 Maybe_1) Bool)
(declare-fun projJust_3 (Q_0 Maybe_1) Bool)
(declare-fun isNothing_1 (Maybe_1) Bool)
(declare-fun isJust_1 (Maybe_1) Bool)
(assert (forall ((x_227 Q_0))
	(projJust_3 x_227 (Just_1 x_227))))
(assert (isNothing_1 Nothing_1))
(assert (forall ((x_229 Q_0))
	(isJust_1 (Just_1 x_229))))
(assert (forall ((x_230 Q_0))
	(diseqMaybe_1 Nothing_1 (Just_1 x_230))))
(assert (forall ((x_231 Q_0))
	(diseqMaybe_1 (Just_1 x_231) Nothing_1)))
(assert (forall ((x_232 Q_0) (x_233 Q_0))
	(=> (diseqQ_0 x_232 x_233)
	    (diseqMaybe_1 (Just_1 x_232) (Just_1 x_233)))))
(declare-datatypes ((E_0 0)) (((Empty_0 ) (EnqL_0 (projEnqL_0 Nat_0) (projEnqL_1 E_0)) (EnqR_0 (projEnqR_0 E_0) (projEnqR_1 Nat_0)) (DeqL_0 (projDeqL_0 E_0)) (DeqR_0 (projDeqR_0 E_0)) (App_0 (projApp_0 E_0) (projApp_1 E_0)))))
(declare-fun diseqE_0 (E_0 E_0) Bool)
(declare-fun projEnqL_2 (Nat_0 E_0) Bool)
(declare-fun projEnqL_3 (E_0 E_0) Bool)
(declare-fun projEnqR_2 (E_0 E_0) Bool)
(declare-fun projEnqR_3 (Nat_0 E_0) Bool)
(declare-fun projDeqL_1 (E_0 E_0) Bool)
(declare-fun projDeqR_1 (E_0 E_0) Bool)
(declare-fun projApp_2 (E_0 E_0) Bool)
(declare-fun projApp_3 (E_0 E_0) Bool)
(declare-fun isEmpty_0 (E_0) Bool)
(declare-fun isEnqL_0 (E_0) Bool)
(declare-fun isEnqR_0 (E_0) Bool)
(declare-fun isDeqL_0 (E_0) Bool)
(declare-fun isDeqR_0 (E_0) Bool)
(declare-fun isApp_0 (E_0) Bool)
(assert (forall ((x_235 Nat_0) (x_236 E_0))
	(projEnqL_2 x_235 (EnqL_0 x_235 x_236))))
(assert (forall ((x_235 Nat_0) (x_236 E_0))
	(projEnqL_3 x_236 (EnqL_0 x_235 x_236))))
(assert (forall ((x_238 E_0) (x_239 Nat_0))
	(projEnqR_2 x_238 (EnqR_0 x_238 x_239))))
(assert (forall ((x_238 E_0) (x_239 Nat_0))
	(projEnqR_3 x_239 (EnqR_0 x_238 x_239))))
(assert (forall ((x_241 E_0))
	(projDeqL_1 x_241 (DeqL_0 x_241))))
(assert (forall ((x_243 E_0))
	(projDeqR_1 x_243 (DeqR_0 x_243))))
(assert (forall ((x_245 E_0) (x_246 E_0))
	(projApp_2 x_245 (App_0 x_245 x_246))))
(assert (forall ((x_245 E_0) (x_246 E_0))
	(projApp_3 x_246 (App_0 x_245 x_246))))
(assert (isEmpty_0 Empty_0))
(assert (forall ((x_248 Nat_0) (x_249 E_0))
	(isEnqL_0 (EnqL_0 x_248 x_249))))
(assert (forall ((x_250 E_0) (x_251 Nat_0))
	(isEnqR_0 (EnqR_0 x_250 x_251))))
(assert (forall ((x_252 E_0))
	(isDeqL_0 (DeqL_0 x_252))))
(assert (forall ((x_253 E_0))
	(isDeqR_0 (DeqR_0 x_253))))
(assert (forall ((x_254 E_0) (x_255 E_0))
	(isApp_0 (App_0 x_254 x_255))))
(assert (forall ((x_256 Nat_0) (x_257 E_0))
	(diseqE_0 Empty_0 (EnqL_0 x_256 x_257))))
(assert (forall ((x_258 E_0) (x_259 Nat_0))
	(diseqE_0 Empty_0 (EnqR_0 x_258 x_259))))
(assert (forall ((x_260 E_0))
	(diseqE_0 Empty_0 (DeqL_0 x_260))))
(assert (forall ((x_261 E_0))
	(diseqE_0 Empty_0 (DeqR_0 x_261))))
(assert (forall ((x_262 E_0) (x_263 E_0))
	(diseqE_0 Empty_0 (App_0 x_262 x_263))))
(assert (forall ((x_264 Nat_0) (x_265 E_0))
	(diseqE_0 (EnqL_0 x_264 x_265) Empty_0)))
(assert (forall ((x_266 E_0) (x_267 Nat_0))
	(diseqE_0 (EnqR_0 x_266 x_267) Empty_0)))
(assert (forall ((x_268 E_0))
	(diseqE_0 (DeqL_0 x_268) Empty_0)))
(assert (forall ((x_269 E_0))
	(diseqE_0 (DeqR_0 x_269) Empty_0)))
(assert (forall ((x_270 E_0) (x_271 E_0))
	(diseqE_0 (App_0 x_270 x_271) Empty_0)))
(assert (forall ((x_272 Nat_0) (x_273 E_0) (x_274 E_0) (x_275 Nat_0))
	(diseqE_0 (EnqL_0 x_272 x_273) (EnqR_0 x_274 x_275))))
(assert (forall ((x_276 Nat_0) (x_277 E_0) (x_278 E_0))
	(diseqE_0 (EnqL_0 x_276 x_277) (DeqL_0 x_278))))
(assert (forall ((x_279 Nat_0) (x_280 E_0) (x_281 E_0))
	(diseqE_0 (EnqL_0 x_279 x_280) (DeqR_0 x_281))))
(assert (forall ((x_282 Nat_0) (x_283 E_0) (x_284 E_0) (x_285 E_0))
	(diseqE_0 (EnqL_0 x_282 x_283) (App_0 x_284 x_285))))
(assert (forall ((x_286 E_0) (x_287 Nat_0) (x_288 Nat_0) (x_289 E_0))
	(diseqE_0 (EnqR_0 x_286 x_287) (EnqL_0 x_288 x_289))))
(assert (forall ((x_290 E_0) (x_291 Nat_0) (x_292 E_0))
	(diseqE_0 (DeqL_0 x_290) (EnqL_0 x_291 x_292))))
(assert (forall ((x_293 E_0) (x_294 Nat_0) (x_295 E_0))
	(diseqE_0 (DeqR_0 x_293) (EnqL_0 x_294 x_295))))
(assert (forall ((x_296 E_0) (x_297 E_0) (x_298 Nat_0) (x_299 E_0))
	(diseqE_0 (App_0 x_296 x_297) (EnqL_0 x_298 x_299))))
(assert (forall ((x_300 E_0) (x_301 Nat_0) (x_302 E_0))
	(diseqE_0 (EnqR_0 x_300 x_301) (DeqL_0 x_302))))
(assert (forall ((x_303 E_0) (x_304 Nat_0) (x_305 E_0))
	(diseqE_0 (EnqR_0 x_303 x_304) (DeqR_0 x_305))))
(assert (forall ((x_306 E_0) (x_307 Nat_0) (x_308 E_0) (x_309 E_0))
	(diseqE_0 (EnqR_0 x_306 x_307) (App_0 x_308 x_309))))
(assert (forall ((x_310 E_0) (x_311 E_0) (x_312 Nat_0))
	(diseqE_0 (DeqL_0 x_310) (EnqR_0 x_311 x_312))))
(assert (forall ((x_313 E_0) (x_314 E_0) (x_315 Nat_0))
	(diseqE_0 (DeqR_0 x_313) (EnqR_0 x_314 x_315))))
(assert (forall ((x_316 E_0) (x_317 E_0) (x_318 E_0) (x_319 Nat_0))
	(diseqE_0 (App_0 x_316 x_317) (EnqR_0 x_318 x_319))))
(assert (forall ((x_320 E_0) (x_321 E_0))
	(diseqE_0 (DeqL_0 x_320) (DeqR_0 x_321))))
(assert (forall ((x_322 E_0) (x_323 E_0) (x_324 E_0))
	(diseqE_0 (DeqL_0 x_322) (App_0 x_323 x_324))))
(assert (forall ((x_325 E_0) (x_326 E_0))
	(diseqE_0 (DeqR_0 x_325) (DeqL_0 x_326))))
(assert (forall ((x_327 E_0) (x_328 E_0) (x_329 E_0))
	(diseqE_0 (App_0 x_327 x_328) (DeqL_0 x_329))))
(assert (forall ((x_330 E_0) (x_331 E_0) (x_332 E_0))
	(diseqE_0 (DeqR_0 x_330) (App_0 x_331 x_332))))
(assert (forall ((x_333 E_0) (x_334 E_0) (x_335 E_0))
	(diseqE_0 (App_0 x_333 x_334) (DeqR_0 x_335))))
(assert (forall ((x_336 Nat_0) (x_337 E_0) (x_338 Nat_0) (x_339 E_0))
	(=> (diseqNat_0 x_336 x_338)
	    (diseqE_0 (EnqL_0 x_336 x_337) (EnqL_0 x_338 x_339)))))
(assert (forall ((x_336 Nat_0) (x_337 E_0) (x_338 Nat_0) (x_339 E_0))
	(=> (diseqE_0 x_337 x_339)
	    (diseqE_0 (EnqL_0 x_336 x_337) (EnqL_0 x_338 x_339)))))
(assert (forall ((x_340 E_0) (x_341 Nat_0) (x_342 E_0) (x_343 Nat_0))
	(=> (diseqE_0 x_340 x_342)
	    (diseqE_0 (EnqR_0 x_340 x_341) (EnqR_0 x_342 x_343)))))
(assert (forall ((x_340 E_0) (x_341 Nat_0) (x_342 E_0) (x_343 Nat_0))
	(=> (diseqNat_0 x_341 x_343)
	    (diseqE_0 (EnqR_0 x_340 x_341) (EnqR_0 x_342 x_343)))))
(assert (forall ((x_344 E_0) (x_345 E_0))
	(=> (diseqE_0 x_344 x_345)
	    (diseqE_0 (DeqL_0 x_344) (DeqL_0 x_345)))))
(assert (forall ((x_346 E_0) (x_347 E_0))
	(=> (diseqE_0 x_346 x_347)
	    (diseqE_0 (DeqR_0 x_346) (DeqR_0 x_347)))))
(assert (forall ((x_348 E_0) (x_349 E_0) (x_350 E_0) (x_351 E_0))
	(=> (diseqE_0 x_348 x_350)
	    (diseqE_0 (App_0 x_348 x_349) (App_0 x_350 x_351)))))
(assert (forall ((x_348 E_0) (x_349 E_0) (x_350 E_0) (x_351 E_0))
	(=> (diseqE_0 x_349 x_351)
	    (diseqE_0 (App_0 x_348 x_349) (App_0 x_350 x_351)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_0 Nat_0) (y_0 list_0))
	(=> (le_0 x_0 Z_13)
	    (take_0 nil_0 x_0 y_0))))
(assert (forall ((x_165 Nat_0) (x_46 list_0) (z_0 Nat_0) (xs_0 list_0) (x_0 Nat_0))
	(=>	(and (gt_0 x_0 Z_13)
			(take_0 x_46 x_165 xs_0)
			(minus_0 x_165 x_0 (Z_14 Z_13)))
		(take_0 (cons_0 z_0 x_46) x_0 (cons_0 z_0 xs_0)))))
(assert (forall ((x_0 Nat_0) (y_0 list_0))
	(=> (le_0 x_0 Z_13)
	    (take_0 nil_0 x_0 y_0))))
(assert (forall ((x_0 Nat_0))
	(=> (gt_0 x_0 Z_13)
	    (take_0 nil_0 x_0 nil_0))))
(declare-fun tail_1 (list_0 list_0) Bool)
(assert (forall ((x_49 list_0) (y_1 Nat_0))
	(tail_1 x_49 (cons_0 y_1 x_49))))
(assert (tail_1 nil_0 nil_0))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_166 Nat_0) (x_52 Nat_0) (y_2 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_52 l_0)
			(add_0 x_166 (Z_14 Z_13) x_52))
		(length_0 x_166 (cons_0 y_2 l_0)))))
(assert (length_0 Z_13 nil_0))
(declare-fun init_0 (list_0 list_0) Bool)
(assert (forall ((x_55 list_0) (x_4 Nat_0) (x_5 list_0) (y_3 Nat_0))
	(=> (init_0 x_55 (cons_0 x_4 x_5))
	    (init_0 (cons_0 y_3 x_55) (cons_0 y_3 (cons_0 x_4 x_5))))))
(assert (forall ((y_3 Nat_0))
	(init_0 nil_0 (cons_0 y_3 nil_0))))
(assert (init_0 nil_0 nil_0))
(declare-fun fstL_0 (Maybe_0 Q_0) Bool)
(assert (forall ((x_10 Nat_0) (x_11 list_0) (z_2 list_0))
	(fstL_0 (Just_0 x_10) (Q_1 (cons_0 x_10 x_11) z_2))))
(assert (forall ((x_8 Nat_0) (x_9 list_0) (y_5 Nat_0))
	(fstL_0 Nothing_0 (Q_1 nil_0 (cons_0 y_5 (cons_0 x_8 x_9))))))
(assert (forall ((y_5 Nat_0))
	(fstL_0 (Just_0 y_5) (Q_1 nil_0 (cons_0 y_5 nil_0)))))
(assert (fstL_0 Nothing_0 (Q_1 nil_0 nil_0)))
(declare-fun fromMaybe_0 (Nat_0 Nat_0 Maybe_0) Bool)
(assert (forall ((x_62 Nat_0) (x_12 Nat_0))
	(fromMaybe_0 x_62 x_12 (Just_0 x_62))))
(assert (forall ((x_12 Nat_0))
	(fromMaybe_0 x_12 x_12 Nothing_0)))
(declare-fun fromMaybe_1 (Q_0 Q_0 Maybe_1) Bool)
(assert (forall ((x_64 Q_0) (x_13 Q_0))
	(fromMaybe_1 x_64 x_13 (Just_1 x_64))))
(assert (forall ((x_13 Q_0))
	(fromMaybe_1 x_13 x_13 Nothing_1)))
(declare-fun empty_1 (Q_0) Bool)
(assert (empty_1 (Q_1 nil_0 nil_0)))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_67 list_0) (x_14 Nat_0))
	(=> (le_0 x_14 Z_13)
	    (drop_0 x_67 x_14 x_67))))
(assert (forall ((x_167 Nat_0) (x_68 list_0) (z_5 Nat_0) (xs_2 list_0) (x_14 Nat_0))
	(=>	(and (gt_0 x_14 Z_13)
			(drop_0 x_68 x_167 xs_2)
			(minus_0 x_167 x_14 (Z_14 Z_13)))
		(drop_0 x_68 x_14 (cons_0 z_5 xs_2)))))
(assert (forall ((x_70 list_0) (x_14 Nat_0))
	(=> (le_0 x_14 Z_13)
	    (drop_0 x_70 x_14 x_70))))
(assert (forall ((x_14 Nat_0))
	(=> (gt_0 x_14 Z_13)
	    (drop_0 nil_0 x_14 nil_0))))
(declare-fun halve_0 (pair_2 list_0) Bool)
(assert (forall ((x_74 list_0) (x_75 list_0) (x_72 Nat_0) (k_0 Nat_0) (x_15 list_0))
	(=>	(and (take_0 x_74 k_0 x_15)
			(drop_0 x_75 k_0 x_15)
			(length_0 x_72 x_15)
			(div_0 k_0 x_72 (Z_14 (Z_14 Z_13))))
		(halve_0 (pair_3 x_74 x_75) x_15))))
(declare-fun x_16 (list_0 list_0 list_0) Bool)
(assert (forall ((x_77 list_0) (z_6 Nat_0) (xs_3 list_0) (y_9 list_0))
	(=> (x_16 x_77 xs_3 y_9)
	    (x_16 (cons_0 z_6 x_77) (cons_0 z_6 xs_3) y_9))))
(assert (forall ((x_78 list_0))
	(x_16 x_78 nil_0 x_78)))
(declare-fun list_1 (list_0 E_0) Bool)
(assert (forall ((x_79 list_0) (x_80 list_0) (x_81 list_0) (a_0 E_0) (b_0 E_0))
	(=>	(and (list_1 x_80 a_0)
			(list_1 x_81 b_0)
			(x_16 x_79 x_80 x_81))
		(list_1 x_79 (App_0 a_0 b_0)))))
(assert (forall ((x_83 list_0) (x_84 list_0) (e_4 E_0))
	(=>	(and (list_1 x_84 e_4)
			(init_0 x_83 x_84))
		(list_1 x_83 (DeqR_0 e_4)))))
(assert (forall ((x_86 list_0) (x_87 list_0) (e_3 E_0))
	(=>	(and (list_1 x_87 e_3)
			(tail_1 x_86 x_87))
		(list_1 x_86 (DeqL_0 e_3)))))
(assert (forall ((x_89 list_0) (x_90 list_0) (e_2 E_0) (z_7 Nat_0))
	(=>	(and (list_1 x_90 e_2)
			(x_16 x_89 x_90 (cons_0 z_7 nil_0)))
		(list_1 x_89 (EnqR_0 e_2 z_7)))))
(assert (forall ((x_93 list_0) (y_10 Nat_0) (e_1 E_0))
	(=> (list_1 x_93 e_1)
	    (list_1 (cons_0 y_10 x_93) (EnqL_0 y_10 e_1)))))
(assert (list_1 nil_0 Empty_0))
(declare-fun reverse_0 (list_0 list_0) Bool)
(assert (forall ((x_95 list_0) (x_96 list_0) (y_11 Nat_0) (xs_4 list_0))
	(=>	(and (reverse_0 x_96 xs_4)
			(x_16 x_95 x_96 (cons_0 y_11 nil_0)))
		(reverse_0 x_95 (cons_0 y_11 xs_4)))))
(assert (reverse_0 nil_0 nil_0))
(declare-fun enqL_1 (Q_0 Nat_0 Q_0) Bool)
(assert (forall ((z_8 Nat_0) (x_21 list_0) (xs_5 list_0) (x_20 Nat_0))
	(enqL_1 (Q_1 (cons_0 x_20 xs_5) (cons_0 z_8 x_21)) x_20 (Q_1 xs_5 (cons_0 z_8 x_21)))))
(assert (forall ((x_102 list_0) (as_0 list_0) (bs_0 list_0) (xs_5 list_0) (x_20 Nat_0))
	(=>	(and (reverse_0 x_102 bs_0)
			(halve_0 (pair_3 as_0 bs_0) (cons_0 x_20 xs_5)))
		(enqL_1 (Q_1 as_0 x_102) x_20 (Q_1 xs_5 nil_0)))))
(declare-fun mkQ_0 (Q_0 list_0 list_0) Bool)
(assert (forall ((x_24 Nat_0) (x_25 list_0) (z_9 Nat_0) (x_23 list_0))
	(mkQ_0 (Q_1 (cons_0 z_9 x_23) (cons_0 x_24 x_25)) (cons_0 z_9 x_23) (cons_0 x_24 x_25))))
(assert (forall ((x_106 list_0) (as_2 list_0) (cs_0 list_0) (z_9 Nat_0) (x_23 list_0))
	(=>	(and (reverse_0 x_106 cs_0)
			(halve_0 (pair_3 as_2 cs_0) (cons_0 z_9 x_23)))
		(mkQ_0 (Q_1 as_2 x_106) (cons_0 z_9 x_23) nil_0))))
(assert (forall ((x_109 list_0) (as_1 list_0) (bs_1 list_0) (y_13 list_0))
	(=>	(and (reverse_0 x_109 as_1)
			(halve_0 (pair_3 as_1 bs_1) y_13))
		(mkQ_0 (Q_1 x_109 bs_1) nil_0 y_13))))
(declare-fun x_26 (Q_0 Q_0 Q_0) Bool)
(assert (forall ((x_110 Q_0) (x_111 list_0) (x_112 list_0) (x_113 list_0) (x_114 list_0) (vs_0 list_0) (ws_0 list_0) (xs_6 list_0) (ys_1 list_0))
	(=>	(and (reverse_0 x_111 ys_1)
			(x_16 x_112 xs_6 x_111)
			(reverse_0 x_113 vs_0)
			(x_16 x_114 ws_0 x_113)
			(mkQ_0 x_110 x_112 x_114))
		(x_26 x_110 (Q_1 xs_6 ys_1) (Q_1 vs_0 ws_0)))))
(declare-fun deqL_1 (Maybe_1 Q_0) Bool)
(assert (forall ((x_117 Q_0) (x_33 Nat_0) (xs_7 list_0) (z_10 list_0))
	(=> (mkQ_0 x_117 xs_7 z_10)
	    (deqL_1 (Just_1 x_117) (Q_1 (cons_0 x_33 xs_7) z_10)))))
(assert (forall ((x_31 Nat_0) (x_32 list_0) (x_29 Nat_0))
	(deqL_1 Nothing_1 (Q_1 nil_0 (cons_0 x_29 (cons_0 x_31 x_32))))))
(assert (forall ((x_120 Q_0) (x_29 Nat_0))
	(=> (empty_1 x_120)
	    (deqL_1 (Just_1 x_120) (Q_1 nil_0 (cons_0 x_29 nil_0))))))
(assert (deqL_1 Nothing_1 (Q_1 nil_0 nil_0)))
(declare-fun deqR_1 (Maybe_1 Q_0) Bool)
(assert (forall ((x_122 Q_0) (x_39 Nat_0) (x_40 list_0) (x_35 Nat_0) (y_17 Nat_0) (ys_2 list_0))
	(=> (mkQ_0 x_122 (cons_0 x_35 (cons_0 x_39 x_40)) ys_2)
	    (deqR_1 (Just_1 x_122) (Q_1 (cons_0 x_35 (cons_0 x_39 x_40)) (cons_0 y_17 ys_2))))))
(assert (forall ((x_124 Q_0) (x_37 Nat_0) (x_38 list_0) (x_35 Nat_0))
	(=> (mkQ_0 x_124 (cons_0 x_35 nil_0) x_38)
	    (deqR_1 (Just_1 x_124) (Q_1 (cons_0 x_35 nil_0) (cons_0 x_37 x_38))))))
(assert (forall ((x_129 Q_0) (y_17 Nat_0) (ys_2 list_0))
	(=> (mkQ_0 x_129 nil_0 ys_2)
	    (deqR_1 (Just_1 x_129) (Q_1 nil_0 (cons_0 y_17 ys_2))))))
(assert (forall ((x_39 Nat_0) (x_40 list_0) (x_35 Nat_0))
	(deqR_1 Nothing_1 (Q_1 (cons_0 x_35 (cons_0 x_39 x_40)) nil_0))))
(assert (forall ((x_134 Q_0) (x_35 Nat_0))
	(=> (empty_1 x_134)
	    (deqR_1 (Just_1 x_134) (Q_1 (cons_0 x_35 nil_0) nil_0)))))
(assert (deqR_1 Nothing_1 (Q_1 nil_0 nil_0)))
(declare-fun enqR_1 (Q_0 Q_0 Nat_0) Bool)
(assert (forall ((x_136 Q_0) (xs_8 list_0) (ys_3 list_0) (y_18 Nat_0))
	(=> (mkQ_0 x_136 xs_8 (cons_0 y_18 ys_3))
	    (enqR_1 x_136 (Q_1 xs_8 ys_3) y_18))))
(declare-fun queue_0 (Q_0 E_0) Bool)
(assert (forall ((x_138 Q_0) (x_139 Q_0) (x_140 Q_0) (a_1 E_0) (b_1 E_0))
	(=>	(and (queue_0 x_139 a_1)
			(queue_0 x_140 b_1)
			(x_26 x_138 x_139 x_140))
		(queue_0 x_138 (App_0 a_1 b_1)))))
(assert (forall ((x_143 Q_0) (x_144 Maybe_1) (r_0 Q_0) (e_8 E_0))
	(=>	(and (deqR_1 x_144 r_0)
			(fromMaybe_1 x_143 r_0 x_144)
			(queue_0 r_0 e_8))
		(queue_0 x_143 (DeqR_0 e_8)))))
(assert (forall ((x_147 Q_0) (x_148 Maybe_1) (q_2 Q_0) (e_7 E_0))
	(=>	(and (deqL_1 x_148 q_2)
			(fromMaybe_1 x_147 q_2 x_148)
			(queue_0 q_2 e_7))
		(queue_0 x_147 (DeqL_0 e_7)))))
(assert (forall ((x_150 Q_0) (x_151 Q_0) (e_6 E_0) (z_12 Nat_0))
	(=>	(and (queue_0 x_151 e_6)
			(enqR_1 x_150 x_151 z_12))
		(queue_0 x_150 (EnqR_0 e_6 z_12)))))
(assert (forall ((x_153 Q_0) (x_154 Q_0) (y_19 Nat_0) (e_5 E_0))
	(=>	(and (queue_0 x_154 e_5)
			(enqL_1 x_153 y_19 x_154))
		(queue_0 x_153 (EnqL_0 y_19 e_5)))))
(assert (forall ((x_156 Q_0))
	(=> (empty_1 x_156)
	    (queue_0 x_156 Empty_0))))
(assert (forall ((x_158 Q_0) (x_159 Maybe_0) (x_43 Nat_0) (y_20 list_0) (e_9 E_0))
	(=>	(and (diseqMaybe_0 x_159 (Just_0 x_43))
			(list_1 (cons_0 x_43 y_20) e_9)
			(queue_0 x_158 e_9)
			(fstL_0 x_159 x_158))
		false)))
(assert (forall ((x_161 Q_0) (x_162 Maybe_0) (e_9 E_0))
	(=>	(and (diseqMaybe_0 x_162 Nothing_0)
			(list_1 nil_0 e_9)
			(queue_0 x_161 e_9)
			(fstL_0 x_162 x_161))
		false)))
(check-sat)
