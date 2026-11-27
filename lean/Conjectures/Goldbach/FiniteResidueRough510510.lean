import Mathlib

private def candidates : List ℕ := [3,5,7,11,41,61,79,149,167,769,1747,2297,2311]
private def covered (k : ℕ) : Bool :=
  candidates.any fun p => (2*k+510510-p).gcd 510510 == 1

private def block (s : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => block s n && covered (s+n)

private theorem block_sound {s n k : ℕ} (h : block s n = true)
    (lo : s ≤ k) (hi : k < s+n) : covered k = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
    by_cases e : k = s+n
    · simpa [e] using h₂
    · exact ih h₁ (by omega)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
private theorem block_0 : block 0 512 = true := by decide
private theorem block_1 : block 512 512 = true := by decide
private theorem block_2 : block 1024 512 = true := by decide
private theorem block_3 : block 1536 512 = true := by decide
private theorem block_4 : block 2048 512 = true := by decide
private theorem block_5 : block 2560 512 = true := by decide
private theorem block_6 : block 3072 512 = true := by decide
private theorem block_7 : block 3584 512 = true := by decide
private theorem block_8 : block 4096 512 = true := by decide
private theorem block_9 : block 4608 512 = true := by decide
private theorem block_10 : block 5120 512 = true := by decide
private theorem block_11 : block 5632 512 = true := by decide
private theorem block_12 : block 6144 512 = true := by decide
private theorem block_13 : block 6656 512 = true := by decide
private theorem block_14 : block 7168 512 = true := by decide
private theorem block_15 : block 7680 512 = true := by decide
private theorem block_16 : block 8192 512 = true := by decide
private theorem block_17 : block 8704 512 = true := by decide
private theorem block_18 : block 9216 512 = true := by decide
private theorem block_19 : block 9728 512 = true := by decide
private theorem block_20 : block 10240 512 = true := by decide
private theorem block_21 : block 10752 512 = true := by decide
private theorem block_22 : block 11264 512 = true := by decide
private theorem block_23 : block 11776 512 = true := by decide
private theorem block_24 : block 12288 512 = true := by decide
private theorem block_25 : block 12800 512 = true := by decide
private theorem block_26 : block 13312 512 = true := by decide
private theorem block_27 : block 13824 512 = true := by decide
private theorem block_28 : block 14336 512 = true := by decide
private theorem block_29 : block 14848 512 = true := by decide
private theorem block_30 : block 15360 512 = true := by decide
private theorem block_31 : block 15872 512 = true := by decide
private theorem block_32 : block 16384 512 = true := by decide
private theorem block_33 : block 16896 512 = true := by decide
private theorem block_34 : block 17408 512 = true := by decide
private theorem block_35 : block 17920 512 = true := by decide
private theorem block_36 : block 18432 512 = true := by decide
private theorem block_37 : block 18944 512 = true := by decide
private theorem block_38 : block 19456 512 = true := by decide
private theorem block_39 : block 19968 512 = true := by decide
private theorem block_40 : block 20480 512 = true := by decide
private theorem block_41 : block 20992 512 = true := by decide
private theorem block_42 : block 21504 512 = true := by decide
private theorem block_43 : block 22016 512 = true := by decide
private theorem block_44 : block 22528 512 = true := by decide
private theorem block_45 : block 23040 512 = true := by decide
private theorem block_46 : block 23552 512 = true := by decide
private theorem block_47 : block 24064 512 = true := by decide
private theorem block_48 : block 24576 512 = true := by decide
private theorem block_49 : block 25088 512 = true := by decide
private theorem block_50 : block 25600 512 = true := by decide
private theorem block_51 : block 26112 512 = true := by decide
private theorem block_52 : block 26624 512 = true := by decide
private theorem block_53 : block 27136 512 = true := by decide
private theorem block_54 : block 27648 512 = true := by decide
private theorem block_55 : block 28160 512 = true := by decide
private theorem block_56 : block 28672 512 = true := by decide
private theorem block_57 : block 29184 512 = true := by decide
private theorem block_58 : block 29696 512 = true := by decide
private theorem block_59 : block 30208 512 = true := by decide
private theorem block_60 : block 30720 512 = true := by decide
private theorem block_61 : block 31232 512 = true := by decide
private theorem block_62 : block 31744 512 = true := by decide
private theorem block_63 : block 32256 512 = true := by decide
private theorem block_64 : block 32768 512 = true := by decide
private theorem block_65 : block 33280 512 = true := by decide
private theorem block_66 : block 33792 512 = true := by decide
private theorem block_67 : block 34304 512 = true := by decide
private theorem block_68 : block 34816 512 = true := by decide
private theorem block_69 : block 35328 512 = true := by decide
private theorem block_70 : block 35840 512 = true := by decide
private theorem block_71 : block 36352 512 = true := by decide
private theorem block_72 : block 36864 512 = true := by decide
private theorem block_73 : block 37376 512 = true := by decide
private theorem block_74 : block 37888 512 = true := by decide
private theorem block_75 : block 38400 512 = true := by decide
private theorem block_76 : block 38912 512 = true := by decide
private theorem block_77 : block 39424 512 = true := by decide
private theorem block_78 : block 39936 512 = true := by decide
private theorem block_79 : block 40448 512 = true := by decide
private theorem block_80 : block 40960 512 = true := by decide
private theorem block_81 : block 41472 512 = true := by decide
private theorem block_82 : block 41984 512 = true := by decide
private theorem block_83 : block 42496 512 = true := by decide
private theorem block_84 : block 43008 512 = true := by decide
private theorem block_85 : block 43520 512 = true := by decide
private theorem block_86 : block 44032 512 = true := by decide
private theorem block_87 : block 44544 512 = true := by decide
private theorem block_88 : block 45056 512 = true := by decide
private theorem block_89 : block 45568 512 = true := by decide
private theorem block_90 : block 46080 512 = true := by decide
private theorem block_91 : block 46592 512 = true := by decide
private theorem block_92 : block 47104 512 = true := by decide
private theorem block_93 : block 47616 512 = true := by decide
private theorem block_94 : block 48128 512 = true := by decide
private theorem block_95 : block 48640 512 = true := by decide
private theorem block_96 : block 49152 512 = true := by decide
private theorem block_97 : block 49664 512 = true := by decide
private theorem block_98 : block 50176 512 = true := by decide
private theorem block_99 : block 50688 512 = true := by decide
private theorem block_100 : block 51200 512 = true := by decide
private theorem block_101 : block 51712 512 = true := by decide
private theorem block_102 : block 52224 512 = true := by decide
private theorem block_103 : block 52736 512 = true := by decide
private theorem block_104 : block 53248 512 = true := by decide
private theorem block_105 : block 53760 512 = true := by decide
private theorem block_106 : block 54272 512 = true := by decide
private theorem block_107 : block 54784 512 = true := by decide
private theorem block_108 : block 55296 512 = true := by decide
private theorem block_109 : block 55808 512 = true := by decide
private theorem block_110 : block 56320 512 = true := by decide
private theorem block_111 : block 56832 512 = true := by decide
private theorem block_112 : block 57344 512 = true := by decide
private theorem block_113 : block 57856 512 = true := by decide
private theorem block_114 : block 58368 512 = true := by decide
private theorem block_115 : block 58880 512 = true := by decide
private theorem block_116 : block 59392 512 = true := by decide
private theorem block_117 : block 59904 512 = true := by decide
private theorem block_118 : block 60416 512 = true := by decide
private theorem block_119 : block 60928 512 = true := by decide
private theorem block_120 : block 61440 512 = true := by decide
private theorem block_121 : block 61952 512 = true := by decide
private theorem block_122 : block 62464 512 = true := by decide
private theorem block_123 : block 62976 512 = true := by decide
private theorem block_124 : block 63488 512 = true := by decide
private theorem block_125 : block 64000 512 = true := by decide
private theorem block_126 : block 64512 512 = true := by decide
private theorem block_127 : block 65024 512 = true := by decide
private theorem block_128 : block 65536 512 = true := by decide
private theorem block_129 : block 66048 512 = true := by decide
private theorem block_130 : block 66560 512 = true := by decide
private theorem block_131 : block 67072 512 = true := by decide
private theorem block_132 : block 67584 512 = true := by decide
private theorem block_133 : block 68096 512 = true := by decide
private theorem block_134 : block 68608 512 = true := by decide
private theorem block_135 : block 69120 512 = true := by decide
private theorem block_136 : block 69632 512 = true := by decide
private theorem block_137 : block 70144 512 = true := by decide
private theorem block_138 : block 70656 512 = true := by decide
private theorem block_139 : block 71168 512 = true := by decide
private theorem block_140 : block 71680 512 = true := by decide
private theorem block_141 : block 72192 512 = true := by decide
private theorem block_142 : block 72704 512 = true := by decide
private theorem block_143 : block 73216 512 = true := by decide
private theorem block_144 : block 73728 512 = true := by decide
private theorem block_145 : block 74240 512 = true := by decide
private theorem block_146 : block 74752 512 = true := by decide
private theorem block_147 : block 75264 512 = true := by decide
private theorem block_148 : block 75776 512 = true := by decide
private theorem block_149 : block 76288 512 = true := by decide
private theorem block_150 : block 76800 512 = true := by decide
private theorem block_151 : block 77312 512 = true := by decide
private theorem block_152 : block 77824 512 = true := by decide
private theorem block_153 : block 78336 512 = true := by decide
private theorem block_154 : block 78848 512 = true := by decide
private theorem block_155 : block 79360 512 = true := by decide
private theorem block_156 : block 79872 512 = true := by decide
private theorem block_157 : block 80384 512 = true := by decide
private theorem block_158 : block 80896 512 = true := by decide
private theorem block_159 : block 81408 512 = true := by decide
private theorem block_160 : block 81920 512 = true := by decide
private theorem block_161 : block 82432 512 = true := by decide
private theorem block_162 : block 82944 512 = true := by decide
private theorem block_163 : block 83456 512 = true := by decide
private theorem block_164 : block 83968 512 = true := by decide
private theorem block_165 : block 84480 512 = true := by decide
private theorem block_166 : block 84992 512 = true := by decide
private theorem block_167 : block 85504 512 = true := by decide
private theorem block_168 : block 86016 512 = true := by decide
private theorem block_169 : block 86528 512 = true := by decide
private theorem block_170 : block 87040 512 = true := by decide
private theorem block_171 : block 87552 512 = true := by decide
private theorem block_172 : block 88064 512 = true := by decide
private theorem block_173 : block 88576 512 = true := by decide
private theorem block_174 : block 89088 512 = true := by decide
private theorem block_175 : block 89600 512 = true := by decide
private theorem block_176 : block 90112 512 = true := by decide
private theorem block_177 : block 90624 512 = true := by decide
private theorem block_178 : block 91136 512 = true := by decide
private theorem block_179 : block 91648 512 = true := by decide
private theorem block_180 : block 92160 512 = true := by decide
private theorem block_181 : block 92672 512 = true := by decide
private theorem block_182 : block 93184 512 = true := by decide
private theorem block_183 : block 93696 512 = true := by decide
private theorem block_184 : block 94208 512 = true := by decide
private theorem block_185 : block 94720 512 = true := by decide
private theorem block_186 : block 95232 512 = true := by decide
private theorem block_187 : block 95744 512 = true := by decide
private theorem block_188 : block 96256 512 = true := by decide
private theorem block_189 : block 96768 512 = true := by decide
private theorem block_190 : block 97280 512 = true := by decide
private theorem block_191 : block 97792 512 = true := by decide
private theorem block_192 : block 98304 512 = true := by decide
private theorem block_193 : block 98816 512 = true := by decide
private theorem block_194 : block 99328 512 = true := by decide
private theorem block_195 : block 99840 512 = true := by decide
private theorem block_196 : block 100352 512 = true := by decide
private theorem block_197 : block 100864 512 = true := by decide
private theorem block_198 : block 101376 512 = true := by decide
private theorem block_199 : block 101888 512 = true := by decide
private theorem block_200 : block 102400 512 = true := by decide
private theorem block_201 : block 102912 512 = true := by decide
private theorem block_202 : block 103424 512 = true := by decide
private theorem block_203 : block 103936 512 = true := by decide
private theorem block_204 : block 104448 512 = true := by decide
private theorem block_205 : block 104960 512 = true := by decide
private theorem block_206 : block 105472 512 = true := by decide
private theorem block_207 : block 105984 512 = true := by decide
private theorem block_208 : block 106496 512 = true := by decide
private theorem block_209 : block 107008 512 = true := by decide
private theorem block_210 : block 107520 512 = true := by decide
private theorem block_211 : block 108032 512 = true := by decide
private theorem block_212 : block 108544 512 = true := by decide
private theorem block_213 : block 109056 512 = true := by decide
private theorem block_214 : block 109568 512 = true := by decide
private theorem block_215 : block 110080 512 = true := by decide
private theorem block_216 : block 110592 512 = true := by decide
private theorem block_217 : block 111104 512 = true := by decide
private theorem block_218 : block 111616 512 = true := by decide
private theorem block_219 : block 112128 512 = true := by decide
private theorem block_220 : block 112640 512 = true := by decide
private theorem block_221 : block 113152 512 = true := by decide
private theorem block_222 : block 113664 512 = true := by decide
private theorem block_223 : block 114176 512 = true := by decide
private theorem block_224 : block 114688 512 = true := by decide
private theorem block_225 : block 115200 512 = true := by decide
private theorem block_226 : block 115712 512 = true := by decide
private theorem block_227 : block 116224 512 = true := by decide
private theorem block_228 : block 116736 512 = true := by decide
private theorem block_229 : block 117248 512 = true := by decide
private theorem block_230 : block 117760 512 = true := by decide
private theorem block_231 : block 118272 512 = true := by decide
private theorem block_232 : block 118784 512 = true := by decide
private theorem block_233 : block 119296 512 = true := by decide
private theorem block_234 : block 119808 512 = true := by decide
private theorem block_235 : block 120320 512 = true := by decide
private theorem block_236 : block 120832 512 = true := by decide
private theorem block_237 : block 121344 512 = true := by decide
private theorem block_238 : block 121856 512 = true := by decide
private theorem block_239 : block 122368 512 = true := by decide
private theorem block_240 : block 122880 512 = true := by decide
private theorem block_241 : block 123392 512 = true := by decide
private theorem block_242 : block 123904 512 = true := by decide
private theorem block_243 : block 124416 512 = true := by decide
private theorem block_244 : block 124928 512 = true := by decide
private theorem block_245 : block 125440 512 = true := by decide
private theorem block_246 : block 125952 512 = true := by decide
private theorem block_247 : block 126464 512 = true := by decide
private theorem block_248 : block 126976 512 = true := by decide
private theorem block_249 : block 127488 512 = true := by decide
private theorem block_250 : block 128000 512 = true := by decide
private theorem block_251 : block 128512 512 = true := by decide
private theorem block_252 : block 129024 512 = true := by decide
private theorem block_253 : block 129536 512 = true := by decide
private theorem block_254 : block 130048 512 = true := by decide
private theorem block_255 : block 130560 512 = true := by decide
private theorem block_256 : block 131072 512 = true := by decide
private theorem block_257 : block 131584 512 = true := by decide
private theorem block_258 : block 132096 512 = true := by decide
private theorem block_259 : block 132608 512 = true := by decide
private theorem block_260 : block 133120 512 = true := by decide
private theorem block_261 : block 133632 512 = true := by decide
private theorem block_262 : block 134144 512 = true := by decide
private theorem block_263 : block 134656 512 = true := by decide
private theorem block_264 : block 135168 512 = true := by decide
private theorem block_265 : block 135680 512 = true := by decide
private theorem block_266 : block 136192 512 = true := by decide
private theorem block_267 : block 136704 512 = true := by decide
private theorem block_268 : block 137216 512 = true := by decide
private theorem block_269 : block 137728 512 = true := by decide
private theorem block_270 : block 138240 512 = true := by decide
private theorem block_271 : block 138752 512 = true := by decide
private theorem block_272 : block 139264 512 = true := by decide
private theorem block_273 : block 139776 512 = true := by decide
private theorem block_274 : block 140288 512 = true := by decide
private theorem block_275 : block 140800 512 = true := by decide
private theorem block_276 : block 141312 512 = true := by decide
private theorem block_277 : block 141824 512 = true := by decide
private theorem block_278 : block 142336 512 = true := by decide
private theorem block_279 : block 142848 512 = true := by decide
private theorem block_280 : block 143360 512 = true := by decide
private theorem block_281 : block 143872 512 = true := by decide
private theorem block_282 : block 144384 512 = true := by decide
private theorem block_283 : block 144896 512 = true := by decide
private theorem block_284 : block 145408 512 = true := by decide
private theorem block_285 : block 145920 512 = true := by decide
private theorem block_286 : block 146432 512 = true := by decide
private theorem block_287 : block 146944 512 = true := by decide
private theorem block_288 : block 147456 512 = true := by decide
private theorem block_289 : block 147968 512 = true := by decide
private theorem block_290 : block 148480 512 = true := by decide
private theorem block_291 : block 148992 512 = true := by decide
private theorem block_292 : block 149504 512 = true := by decide
private theorem block_293 : block 150016 512 = true := by decide
private theorem block_294 : block 150528 512 = true := by decide
private theorem block_295 : block 151040 512 = true := by decide
private theorem block_296 : block 151552 512 = true := by decide
private theorem block_297 : block 152064 512 = true := by decide
private theorem block_298 : block 152576 512 = true := by decide
private theorem block_299 : block 153088 512 = true := by decide
private theorem block_300 : block 153600 512 = true := by decide
private theorem block_301 : block 154112 512 = true := by decide
private theorem block_302 : block 154624 512 = true := by decide
private theorem block_303 : block 155136 512 = true := by decide
private theorem block_304 : block 155648 512 = true := by decide
private theorem block_305 : block 156160 512 = true := by decide
private theorem block_306 : block 156672 512 = true := by decide
private theorem block_307 : block 157184 512 = true := by decide
private theorem block_308 : block 157696 512 = true := by decide
private theorem block_309 : block 158208 512 = true := by decide
private theorem block_310 : block 158720 512 = true := by decide
private theorem block_311 : block 159232 512 = true := by decide
private theorem block_312 : block 159744 512 = true := by decide
private theorem block_313 : block 160256 512 = true := by decide
private theorem block_314 : block 160768 512 = true := by decide
private theorem block_315 : block 161280 512 = true := by decide
private theorem block_316 : block 161792 512 = true := by decide
private theorem block_317 : block 162304 512 = true := by decide
private theorem block_318 : block 162816 512 = true := by decide
private theorem block_319 : block 163328 512 = true := by decide
private theorem block_320 : block 163840 512 = true := by decide
private theorem block_321 : block 164352 512 = true := by decide
private theorem block_322 : block 164864 512 = true := by decide
private theorem block_323 : block 165376 512 = true := by decide
private theorem block_324 : block 165888 512 = true := by decide
private theorem block_325 : block 166400 512 = true := by decide
private theorem block_326 : block 166912 512 = true := by decide
private theorem block_327 : block 167424 512 = true := by decide
private theorem block_328 : block 167936 512 = true := by decide
private theorem block_329 : block 168448 512 = true := by decide
private theorem block_330 : block 168960 512 = true := by decide
private theorem block_331 : block 169472 512 = true := by decide
private theorem block_332 : block 169984 512 = true := by decide
private theorem block_333 : block 170496 512 = true := by decide
private theorem block_334 : block 171008 512 = true := by decide
private theorem block_335 : block 171520 512 = true := by decide
private theorem block_336 : block 172032 512 = true := by decide
private theorem block_337 : block 172544 512 = true := by decide
private theorem block_338 : block 173056 512 = true := by decide
private theorem block_339 : block 173568 512 = true := by decide
private theorem block_340 : block 174080 512 = true := by decide
private theorem block_341 : block 174592 512 = true := by decide
private theorem block_342 : block 175104 512 = true := by decide
private theorem block_343 : block 175616 512 = true := by decide
private theorem block_344 : block 176128 512 = true := by decide
private theorem block_345 : block 176640 512 = true := by decide
private theorem block_346 : block 177152 512 = true := by decide
private theorem block_347 : block 177664 512 = true := by decide
private theorem block_348 : block 178176 512 = true := by decide
private theorem block_349 : block 178688 512 = true := by decide
private theorem block_350 : block 179200 512 = true := by decide
private theorem block_351 : block 179712 512 = true := by decide
private theorem block_352 : block 180224 512 = true := by decide
private theorem block_353 : block 180736 512 = true := by decide
private theorem block_354 : block 181248 512 = true := by decide
private theorem block_355 : block 181760 512 = true := by decide
private theorem block_356 : block 182272 512 = true := by decide
private theorem block_357 : block 182784 512 = true := by decide
private theorem block_358 : block 183296 512 = true := by decide
private theorem block_359 : block 183808 512 = true := by decide
private theorem block_360 : block 184320 512 = true := by decide
private theorem block_361 : block 184832 512 = true := by decide
private theorem block_362 : block 185344 512 = true := by decide
private theorem block_363 : block 185856 512 = true := by decide
private theorem block_364 : block 186368 512 = true := by decide
private theorem block_365 : block 186880 512 = true := by decide
private theorem block_366 : block 187392 512 = true := by decide
private theorem block_367 : block 187904 512 = true := by decide
private theorem block_368 : block 188416 512 = true := by decide
private theorem block_369 : block 188928 512 = true := by decide
private theorem block_370 : block 189440 512 = true := by decide
private theorem block_371 : block 189952 512 = true := by decide
private theorem block_372 : block 190464 512 = true := by decide
private theorem block_373 : block 190976 512 = true := by decide
private theorem block_374 : block 191488 512 = true := by decide
private theorem block_375 : block 192000 512 = true := by decide
private theorem block_376 : block 192512 512 = true := by decide
private theorem block_377 : block 193024 512 = true := by decide
private theorem block_378 : block 193536 512 = true := by decide
private theorem block_379 : block 194048 512 = true := by decide
private theorem block_380 : block 194560 512 = true := by decide
private theorem block_381 : block 195072 512 = true := by decide
private theorem block_382 : block 195584 512 = true := by decide
private theorem block_383 : block 196096 512 = true := by decide
private theorem block_384 : block 196608 512 = true := by decide
private theorem block_385 : block 197120 512 = true := by decide
private theorem block_386 : block 197632 512 = true := by decide
private theorem block_387 : block 198144 512 = true := by decide
private theorem block_388 : block 198656 512 = true := by decide
private theorem block_389 : block 199168 512 = true := by decide
private theorem block_390 : block 199680 512 = true := by decide
private theorem block_391 : block 200192 512 = true := by decide
private theorem block_392 : block 200704 512 = true := by decide
private theorem block_393 : block 201216 512 = true := by decide
private theorem block_394 : block 201728 512 = true := by decide
private theorem block_395 : block 202240 512 = true := by decide
private theorem block_396 : block 202752 512 = true := by decide
private theorem block_397 : block 203264 512 = true := by decide
private theorem block_398 : block 203776 512 = true := by decide
private theorem block_399 : block 204288 512 = true := by decide
private theorem block_400 : block 204800 512 = true := by decide
private theorem block_401 : block 205312 512 = true := by decide
private theorem block_402 : block 205824 512 = true := by decide
private theorem block_403 : block 206336 512 = true := by decide
private theorem block_404 : block 206848 512 = true := by decide
private theorem block_405 : block 207360 512 = true := by decide
private theorem block_406 : block 207872 512 = true := by decide
private theorem block_407 : block 208384 512 = true := by decide
private theorem block_408 : block 208896 512 = true := by decide
private theorem block_409 : block 209408 512 = true := by decide
private theorem block_410 : block 209920 512 = true := by decide
private theorem block_411 : block 210432 512 = true := by decide
private theorem block_412 : block 210944 512 = true := by decide
private theorem block_413 : block 211456 512 = true := by decide
private theorem block_414 : block 211968 512 = true := by decide
private theorem block_415 : block 212480 512 = true := by decide
private theorem block_416 : block 212992 512 = true := by decide
private theorem block_417 : block 213504 512 = true := by decide
private theorem block_418 : block 214016 512 = true := by decide
private theorem block_419 : block 214528 512 = true := by decide
private theorem block_420 : block 215040 512 = true := by decide
private theorem block_421 : block 215552 512 = true := by decide
private theorem block_422 : block 216064 512 = true := by decide
private theorem block_423 : block 216576 512 = true := by decide
private theorem block_424 : block 217088 512 = true := by decide
private theorem block_425 : block 217600 512 = true := by decide
private theorem block_426 : block 218112 512 = true := by decide
private theorem block_427 : block 218624 512 = true := by decide
private theorem block_428 : block 219136 512 = true := by decide
private theorem block_429 : block 219648 512 = true := by decide
private theorem block_430 : block 220160 512 = true := by decide
private theorem block_431 : block 220672 512 = true := by decide
private theorem block_432 : block 221184 512 = true := by decide
private theorem block_433 : block 221696 512 = true := by decide
private theorem block_434 : block 222208 512 = true := by decide
private theorem block_435 : block 222720 512 = true := by decide
private theorem block_436 : block 223232 512 = true := by decide
private theorem block_437 : block 223744 512 = true := by decide
private theorem block_438 : block 224256 512 = true := by decide
private theorem block_439 : block 224768 512 = true := by decide
private theorem block_440 : block 225280 512 = true := by decide
private theorem block_441 : block 225792 512 = true := by decide
private theorem block_442 : block 226304 512 = true := by decide
private theorem block_443 : block 226816 512 = true := by decide
private theorem block_444 : block 227328 512 = true := by decide
private theorem block_445 : block 227840 512 = true := by decide
private theorem block_446 : block 228352 512 = true := by decide
private theorem block_447 : block 228864 512 = true := by decide
private theorem block_448 : block 229376 512 = true := by decide
private theorem block_449 : block 229888 512 = true := by decide
private theorem block_450 : block 230400 512 = true := by decide
private theorem block_451 : block 230912 512 = true := by decide
private theorem block_452 : block 231424 512 = true := by decide
private theorem block_453 : block 231936 512 = true := by decide
private theorem block_454 : block 232448 512 = true := by decide
private theorem block_455 : block 232960 512 = true := by decide
private theorem block_456 : block 233472 512 = true := by decide
private theorem block_457 : block 233984 512 = true := by decide
private theorem block_458 : block 234496 512 = true := by decide
private theorem block_459 : block 235008 512 = true := by decide
private theorem block_460 : block 235520 512 = true := by decide
private theorem block_461 : block 236032 512 = true := by decide
private theorem block_462 : block 236544 512 = true := by decide
private theorem block_463 : block 237056 512 = true := by decide
private theorem block_464 : block 237568 512 = true := by decide
private theorem block_465 : block 238080 512 = true := by decide
private theorem block_466 : block 238592 512 = true := by decide
private theorem block_467 : block 239104 512 = true := by decide
private theorem block_468 : block 239616 512 = true := by decide
private theorem block_469 : block 240128 512 = true := by decide
private theorem block_470 : block 240640 512 = true := by decide
private theorem block_471 : block 241152 512 = true := by decide
private theorem block_472 : block 241664 512 = true := by decide
private theorem block_473 : block 242176 512 = true := by decide
private theorem block_474 : block 242688 512 = true := by decide
private theorem block_475 : block 243200 512 = true := by decide
private theorem block_476 : block 243712 512 = true := by decide
private theorem block_477 : block 244224 512 = true := by decide
private theorem block_478 : block 244736 512 = true := by decide
private theorem block_479 : block 245248 512 = true := by decide
private theorem block_480 : block 245760 512 = true := by decide
private theorem block_481 : block 246272 512 = true := by decide
private theorem block_482 : block 246784 512 = true := by decide
private theorem block_483 : block 247296 512 = true := by decide
private theorem block_484 : block 247808 512 = true := by decide
private theorem block_485 : block 248320 512 = true := by decide
private theorem block_486 : block 248832 512 = true := by decide
private theorem block_487 : block 249344 512 = true := by decide
private theorem block_488 : block 249856 512 = true := by decide
private theorem block_489 : block 250368 512 = true := by decide
private theorem block_490 : block 250880 512 = true := by decide
private theorem block_491 : block 251392 512 = true := by decide
private theorem block_492 : block 251904 512 = true := by decide
private theorem block_493 : block 252416 512 = true := by decide
private theorem block_494 : block 252928 512 = true := by decide
private theorem block_495 : block 253440 512 = true := by decide
private theorem block_496 : block 253952 512 = true := by decide
private theorem block_497 : block 254464 512 = true := by decide
private theorem block_498 : block 254976 512 = true := by decide
private theorem all_covered (k : ℕ) (hk : k < 255255) : covered k = true := by
  by_cases h_249 : k < 127488
  · by_cases h_124 : k < 63488
    · by_cases h_62 : k < 31744
      · by_cases h_31 : k < 15872
        · by_cases h_15 : k < 7680
          · by_cases h_7 : k < 3584
            · by_cases h_3 : k < 1536
              · by_cases h_1 : k < 512
                · exact block_sound block_0 (by omega) (by omega)
                · by_cases h_2 : k < 1024
                  · exact block_sound block_1 (by omega) (by omega)
                  · exact block_sound block_2 (by omega) (by omega)
              · by_cases h_5 : k < 2560
                · by_cases h_4 : k < 2048
                  · exact block_sound block_3 (by omega) (by omega)
                  · exact block_sound block_4 (by omega) (by omega)
                · by_cases h_6 : k < 3072
                  · exact block_sound block_5 (by omega) (by omega)
                  · exact block_sound block_6 (by omega) (by omega)
            · by_cases h_11 : k < 5632
              · by_cases h_9 : k < 4608
                · by_cases h_8 : k < 4096
                  · exact block_sound block_7 (by omega) (by omega)
                  · exact block_sound block_8 (by omega) (by omega)
                · by_cases h_10 : k < 5120
                  · exact block_sound block_9 (by omega) (by omega)
                  · exact block_sound block_10 (by omega) (by omega)
              · by_cases h_13 : k < 6656
                · by_cases h_12 : k < 6144
                  · exact block_sound block_11 (by omega) (by omega)
                  · exact block_sound block_12 (by omega) (by omega)
                · by_cases h_14 : k < 7168
                  · exact block_sound block_13 (by omega) (by omega)
                  · exact block_sound block_14 (by omega) (by omega)
          · by_cases h_23 : k < 11776
            · by_cases h_19 : k < 9728
              · by_cases h_17 : k < 8704
                · by_cases h_16 : k < 8192
                  · exact block_sound block_15 (by omega) (by omega)
                  · exact block_sound block_16 (by omega) (by omega)
                · by_cases h_18 : k < 9216
                  · exact block_sound block_17 (by omega) (by omega)
                  · exact block_sound block_18 (by omega) (by omega)
              · by_cases h_21 : k < 10752
                · by_cases h_20 : k < 10240
                  · exact block_sound block_19 (by omega) (by omega)
                  · exact block_sound block_20 (by omega) (by omega)
                · by_cases h_22 : k < 11264
                  · exact block_sound block_21 (by omega) (by omega)
                  · exact block_sound block_22 (by omega) (by omega)
            · by_cases h_27 : k < 13824
              · by_cases h_25 : k < 12800
                · by_cases h_24 : k < 12288
                  · exact block_sound block_23 (by omega) (by omega)
                  · exact block_sound block_24 (by omega) (by omega)
                · by_cases h_26 : k < 13312
                  · exact block_sound block_25 (by omega) (by omega)
                  · exact block_sound block_26 (by omega) (by omega)
              · by_cases h_29 : k < 14848
                · by_cases h_28 : k < 14336
                  · exact block_sound block_27 (by omega) (by omega)
                  · exact block_sound block_28 (by omega) (by omega)
                · by_cases h_30 : k < 15360
                  · exact block_sound block_29 (by omega) (by omega)
                  · exact block_sound block_30 (by omega) (by omega)
        · by_cases h_46 : k < 23552
          · by_cases h_38 : k < 19456
            · by_cases h_34 : k < 17408
              · by_cases h_32 : k < 16384
                · exact block_sound block_31 (by omega) (by omega)
                · by_cases h_33 : k < 16896
                  · exact block_sound block_32 (by omega) (by omega)
                  · exact block_sound block_33 (by omega) (by omega)
              · by_cases h_36 : k < 18432
                · by_cases h_35 : k < 17920
                  · exact block_sound block_34 (by omega) (by omega)
                  · exact block_sound block_35 (by omega) (by omega)
                · by_cases h_37 : k < 18944
                  · exact block_sound block_36 (by omega) (by omega)
                  · exact block_sound block_37 (by omega) (by omega)
            · by_cases h_42 : k < 21504
              · by_cases h_40 : k < 20480
                · by_cases h_39 : k < 19968
                  · exact block_sound block_38 (by omega) (by omega)
                  · exact block_sound block_39 (by omega) (by omega)
                · by_cases h_41 : k < 20992
                  · exact block_sound block_40 (by omega) (by omega)
                  · exact block_sound block_41 (by omega) (by omega)
              · by_cases h_44 : k < 22528
                · by_cases h_43 : k < 22016
                  · exact block_sound block_42 (by omega) (by omega)
                  · exact block_sound block_43 (by omega) (by omega)
                · by_cases h_45 : k < 23040
                  · exact block_sound block_44 (by omega) (by omega)
                  · exact block_sound block_45 (by omega) (by omega)
          · by_cases h_54 : k < 27648
            · by_cases h_50 : k < 25600
              · by_cases h_48 : k < 24576
                · by_cases h_47 : k < 24064
                  · exact block_sound block_46 (by omega) (by omega)
                  · exact block_sound block_47 (by omega) (by omega)
                · by_cases h_49 : k < 25088
                  · exact block_sound block_48 (by omega) (by omega)
                  · exact block_sound block_49 (by omega) (by omega)
              · by_cases h_52 : k < 26624
                · by_cases h_51 : k < 26112
                  · exact block_sound block_50 (by omega) (by omega)
                  · exact block_sound block_51 (by omega) (by omega)
                · by_cases h_53 : k < 27136
                  · exact block_sound block_52 (by omega) (by omega)
                  · exact block_sound block_53 (by omega) (by omega)
            · by_cases h_58 : k < 29696
              · by_cases h_56 : k < 28672
                · by_cases h_55 : k < 28160
                  · exact block_sound block_54 (by omega) (by omega)
                  · exact block_sound block_55 (by omega) (by omega)
                · by_cases h_57 : k < 29184
                  · exact block_sound block_56 (by omega) (by omega)
                  · exact block_sound block_57 (by omega) (by omega)
              · by_cases h_60 : k < 30720
                · by_cases h_59 : k < 30208
                  · exact block_sound block_58 (by omega) (by omega)
                  · exact block_sound block_59 (by omega) (by omega)
                · by_cases h_61 : k < 31232
                  · exact block_sound block_60 (by omega) (by omega)
                  · exact block_sound block_61 (by omega) (by omega)
      · by_cases h_93 : k < 47616
        · by_cases h_77 : k < 39424
          · by_cases h_69 : k < 35328
            · by_cases h_65 : k < 33280
              · by_cases h_63 : k < 32256
                · exact block_sound block_62 (by omega) (by omega)
                · by_cases h_64 : k < 32768
                  · exact block_sound block_63 (by omega) (by omega)
                  · exact block_sound block_64 (by omega) (by omega)
              · by_cases h_67 : k < 34304
                · by_cases h_66 : k < 33792
                  · exact block_sound block_65 (by omega) (by omega)
                  · exact block_sound block_66 (by omega) (by omega)
                · by_cases h_68 : k < 34816
                  · exact block_sound block_67 (by omega) (by omega)
                  · exact block_sound block_68 (by omega) (by omega)
            · by_cases h_73 : k < 37376
              · by_cases h_71 : k < 36352
                · by_cases h_70 : k < 35840
                  · exact block_sound block_69 (by omega) (by omega)
                  · exact block_sound block_70 (by omega) (by omega)
                · by_cases h_72 : k < 36864
                  · exact block_sound block_71 (by omega) (by omega)
                  · exact block_sound block_72 (by omega) (by omega)
              · by_cases h_75 : k < 38400
                · by_cases h_74 : k < 37888
                  · exact block_sound block_73 (by omega) (by omega)
                  · exact block_sound block_74 (by omega) (by omega)
                · by_cases h_76 : k < 38912
                  · exact block_sound block_75 (by omega) (by omega)
                  · exact block_sound block_76 (by omega) (by omega)
          · by_cases h_85 : k < 43520
            · by_cases h_81 : k < 41472
              · by_cases h_79 : k < 40448
                · by_cases h_78 : k < 39936
                  · exact block_sound block_77 (by omega) (by omega)
                  · exact block_sound block_78 (by omega) (by omega)
                · by_cases h_80 : k < 40960
                  · exact block_sound block_79 (by omega) (by omega)
                  · exact block_sound block_80 (by omega) (by omega)
              · by_cases h_83 : k < 42496
                · by_cases h_82 : k < 41984
                  · exact block_sound block_81 (by omega) (by omega)
                  · exact block_sound block_82 (by omega) (by omega)
                · by_cases h_84 : k < 43008
                  · exact block_sound block_83 (by omega) (by omega)
                  · exact block_sound block_84 (by omega) (by omega)
            · by_cases h_89 : k < 45568
              · by_cases h_87 : k < 44544
                · by_cases h_86 : k < 44032
                  · exact block_sound block_85 (by omega) (by omega)
                  · exact block_sound block_86 (by omega) (by omega)
                · by_cases h_88 : k < 45056
                  · exact block_sound block_87 (by omega) (by omega)
                  · exact block_sound block_88 (by omega) (by omega)
              · by_cases h_91 : k < 46592
                · by_cases h_90 : k < 46080
                  · exact block_sound block_89 (by omega) (by omega)
                  · exact block_sound block_90 (by omega) (by omega)
                · by_cases h_92 : k < 47104
                  · exact block_sound block_91 (by omega) (by omega)
                  · exact block_sound block_92 (by omega) (by omega)
        · by_cases h_108 : k < 55296
          · by_cases h_100 : k < 51200
            · by_cases h_96 : k < 49152
              · by_cases h_94 : k < 48128
                · exact block_sound block_93 (by omega) (by omega)
                · by_cases h_95 : k < 48640
                  · exact block_sound block_94 (by omega) (by omega)
                  · exact block_sound block_95 (by omega) (by omega)
              · by_cases h_98 : k < 50176
                · by_cases h_97 : k < 49664
                  · exact block_sound block_96 (by omega) (by omega)
                  · exact block_sound block_97 (by omega) (by omega)
                · by_cases h_99 : k < 50688
                  · exact block_sound block_98 (by omega) (by omega)
                  · exact block_sound block_99 (by omega) (by omega)
            · by_cases h_104 : k < 53248
              · by_cases h_102 : k < 52224
                · by_cases h_101 : k < 51712
                  · exact block_sound block_100 (by omega) (by omega)
                  · exact block_sound block_101 (by omega) (by omega)
                · by_cases h_103 : k < 52736
                  · exact block_sound block_102 (by omega) (by omega)
                  · exact block_sound block_103 (by omega) (by omega)
              · by_cases h_106 : k < 54272
                · by_cases h_105 : k < 53760
                  · exact block_sound block_104 (by omega) (by omega)
                  · exact block_sound block_105 (by omega) (by omega)
                · by_cases h_107 : k < 54784
                  · exact block_sound block_106 (by omega) (by omega)
                  · exact block_sound block_107 (by omega) (by omega)
          · by_cases h_116 : k < 59392
            · by_cases h_112 : k < 57344
              · by_cases h_110 : k < 56320
                · by_cases h_109 : k < 55808
                  · exact block_sound block_108 (by omega) (by omega)
                  · exact block_sound block_109 (by omega) (by omega)
                · by_cases h_111 : k < 56832
                  · exact block_sound block_110 (by omega) (by omega)
                  · exact block_sound block_111 (by omega) (by omega)
              · by_cases h_114 : k < 58368
                · by_cases h_113 : k < 57856
                  · exact block_sound block_112 (by omega) (by omega)
                  · exact block_sound block_113 (by omega) (by omega)
                · by_cases h_115 : k < 58880
                  · exact block_sound block_114 (by omega) (by omega)
                  · exact block_sound block_115 (by omega) (by omega)
            · by_cases h_120 : k < 61440
              · by_cases h_118 : k < 60416
                · by_cases h_117 : k < 59904
                  · exact block_sound block_116 (by omega) (by omega)
                  · exact block_sound block_117 (by omega) (by omega)
                · by_cases h_119 : k < 60928
                  · exact block_sound block_118 (by omega) (by omega)
                  · exact block_sound block_119 (by omega) (by omega)
              · by_cases h_122 : k < 62464
                · by_cases h_121 : k < 61952
                  · exact block_sound block_120 (by omega) (by omega)
                  · exact block_sound block_121 (by omega) (by omega)
                · by_cases h_123 : k < 62976
                  · exact block_sound block_122 (by omega) (by omega)
                  · exact block_sound block_123 (by omega) (by omega)
    · by_cases h_186 : k < 95232
      · by_cases h_155 : k < 79360
        · by_cases h_139 : k < 71168
          · by_cases h_131 : k < 67072
            · by_cases h_127 : k < 65024
              · by_cases h_125 : k < 64000
                · exact block_sound block_124 (by omega) (by omega)
                · by_cases h_126 : k < 64512
                  · exact block_sound block_125 (by omega) (by omega)
                  · exact block_sound block_126 (by omega) (by omega)
              · by_cases h_129 : k < 66048
                · by_cases h_128 : k < 65536
                  · exact block_sound block_127 (by omega) (by omega)
                  · exact block_sound block_128 (by omega) (by omega)
                · by_cases h_130 : k < 66560
                  · exact block_sound block_129 (by omega) (by omega)
                  · exact block_sound block_130 (by omega) (by omega)
            · by_cases h_135 : k < 69120
              · by_cases h_133 : k < 68096
                · by_cases h_132 : k < 67584
                  · exact block_sound block_131 (by omega) (by omega)
                  · exact block_sound block_132 (by omega) (by omega)
                · by_cases h_134 : k < 68608
                  · exact block_sound block_133 (by omega) (by omega)
                  · exact block_sound block_134 (by omega) (by omega)
              · by_cases h_137 : k < 70144
                · by_cases h_136 : k < 69632
                  · exact block_sound block_135 (by omega) (by omega)
                  · exact block_sound block_136 (by omega) (by omega)
                · by_cases h_138 : k < 70656
                  · exact block_sound block_137 (by omega) (by omega)
                  · exact block_sound block_138 (by omega) (by omega)
          · by_cases h_147 : k < 75264
            · by_cases h_143 : k < 73216
              · by_cases h_141 : k < 72192
                · by_cases h_140 : k < 71680
                  · exact block_sound block_139 (by omega) (by omega)
                  · exact block_sound block_140 (by omega) (by omega)
                · by_cases h_142 : k < 72704
                  · exact block_sound block_141 (by omega) (by omega)
                  · exact block_sound block_142 (by omega) (by omega)
              · by_cases h_145 : k < 74240
                · by_cases h_144 : k < 73728
                  · exact block_sound block_143 (by omega) (by omega)
                  · exact block_sound block_144 (by omega) (by omega)
                · by_cases h_146 : k < 74752
                  · exact block_sound block_145 (by omega) (by omega)
                  · exact block_sound block_146 (by omega) (by omega)
            · by_cases h_151 : k < 77312
              · by_cases h_149 : k < 76288
                · by_cases h_148 : k < 75776
                  · exact block_sound block_147 (by omega) (by omega)
                  · exact block_sound block_148 (by omega) (by omega)
                · by_cases h_150 : k < 76800
                  · exact block_sound block_149 (by omega) (by omega)
                  · exact block_sound block_150 (by omega) (by omega)
              · by_cases h_153 : k < 78336
                · by_cases h_152 : k < 77824
                  · exact block_sound block_151 (by omega) (by omega)
                  · exact block_sound block_152 (by omega) (by omega)
                · by_cases h_154 : k < 78848
                  · exact block_sound block_153 (by omega) (by omega)
                  · exact block_sound block_154 (by omega) (by omega)
        · by_cases h_170 : k < 87040
          · by_cases h_162 : k < 82944
            · by_cases h_158 : k < 80896
              · by_cases h_156 : k < 79872
                · exact block_sound block_155 (by omega) (by omega)
                · by_cases h_157 : k < 80384
                  · exact block_sound block_156 (by omega) (by omega)
                  · exact block_sound block_157 (by omega) (by omega)
              · by_cases h_160 : k < 81920
                · by_cases h_159 : k < 81408
                  · exact block_sound block_158 (by omega) (by omega)
                  · exact block_sound block_159 (by omega) (by omega)
                · by_cases h_161 : k < 82432
                  · exact block_sound block_160 (by omega) (by omega)
                  · exact block_sound block_161 (by omega) (by omega)
            · by_cases h_166 : k < 84992
              · by_cases h_164 : k < 83968
                · by_cases h_163 : k < 83456
                  · exact block_sound block_162 (by omega) (by omega)
                  · exact block_sound block_163 (by omega) (by omega)
                · by_cases h_165 : k < 84480
                  · exact block_sound block_164 (by omega) (by omega)
                  · exact block_sound block_165 (by omega) (by omega)
              · by_cases h_168 : k < 86016
                · by_cases h_167 : k < 85504
                  · exact block_sound block_166 (by omega) (by omega)
                  · exact block_sound block_167 (by omega) (by omega)
                · by_cases h_169 : k < 86528
                  · exact block_sound block_168 (by omega) (by omega)
                  · exact block_sound block_169 (by omega) (by omega)
          · by_cases h_178 : k < 91136
            · by_cases h_174 : k < 89088
              · by_cases h_172 : k < 88064
                · by_cases h_171 : k < 87552
                  · exact block_sound block_170 (by omega) (by omega)
                  · exact block_sound block_171 (by omega) (by omega)
                · by_cases h_173 : k < 88576
                  · exact block_sound block_172 (by omega) (by omega)
                  · exact block_sound block_173 (by omega) (by omega)
              · by_cases h_176 : k < 90112
                · by_cases h_175 : k < 89600
                  · exact block_sound block_174 (by omega) (by omega)
                  · exact block_sound block_175 (by omega) (by omega)
                · by_cases h_177 : k < 90624
                  · exact block_sound block_176 (by omega) (by omega)
                  · exact block_sound block_177 (by omega) (by omega)
            · by_cases h_182 : k < 93184
              · by_cases h_180 : k < 92160
                · by_cases h_179 : k < 91648
                  · exact block_sound block_178 (by omega) (by omega)
                  · exact block_sound block_179 (by omega) (by omega)
                · by_cases h_181 : k < 92672
                  · exact block_sound block_180 (by omega) (by omega)
                  · exact block_sound block_181 (by omega) (by omega)
              · by_cases h_184 : k < 94208
                · by_cases h_183 : k < 93696
                  · exact block_sound block_182 (by omega) (by omega)
                  · exact block_sound block_183 (by omega) (by omega)
                · by_cases h_185 : k < 94720
                  · exact block_sound block_184 (by omega) (by omega)
                  · exact block_sound block_185 (by omega) (by omega)
      · by_cases h_217 : k < 111104
        · by_cases h_201 : k < 102912
          · by_cases h_193 : k < 98816
            · by_cases h_189 : k < 96768
              · by_cases h_187 : k < 95744
                · exact block_sound block_186 (by omega) (by omega)
                · by_cases h_188 : k < 96256
                  · exact block_sound block_187 (by omega) (by omega)
                  · exact block_sound block_188 (by omega) (by omega)
              · by_cases h_191 : k < 97792
                · by_cases h_190 : k < 97280
                  · exact block_sound block_189 (by omega) (by omega)
                  · exact block_sound block_190 (by omega) (by omega)
                · by_cases h_192 : k < 98304
                  · exact block_sound block_191 (by omega) (by omega)
                  · exact block_sound block_192 (by omega) (by omega)
            · by_cases h_197 : k < 100864
              · by_cases h_195 : k < 99840
                · by_cases h_194 : k < 99328
                  · exact block_sound block_193 (by omega) (by omega)
                  · exact block_sound block_194 (by omega) (by omega)
                · by_cases h_196 : k < 100352
                  · exact block_sound block_195 (by omega) (by omega)
                  · exact block_sound block_196 (by omega) (by omega)
              · by_cases h_199 : k < 101888
                · by_cases h_198 : k < 101376
                  · exact block_sound block_197 (by omega) (by omega)
                  · exact block_sound block_198 (by omega) (by omega)
                · by_cases h_200 : k < 102400
                  · exact block_sound block_199 (by omega) (by omega)
                  · exact block_sound block_200 (by omega) (by omega)
          · by_cases h_209 : k < 107008
            · by_cases h_205 : k < 104960
              · by_cases h_203 : k < 103936
                · by_cases h_202 : k < 103424
                  · exact block_sound block_201 (by omega) (by omega)
                  · exact block_sound block_202 (by omega) (by omega)
                · by_cases h_204 : k < 104448
                  · exact block_sound block_203 (by omega) (by omega)
                  · exact block_sound block_204 (by omega) (by omega)
              · by_cases h_207 : k < 105984
                · by_cases h_206 : k < 105472
                  · exact block_sound block_205 (by omega) (by omega)
                  · exact block_sound block_206 (by omega) (by omega)
                · by_cases h_208 : k < 106496
                  · exact block_sound block_207 (by omega) (by omega)
                  · exact block_sound block_208 (by omega) (by omega)
            · by_cases h_213 : k < 109056
              · by_cases h_211 : k < 108032
                · by_cases h_210 : k < 107520
                  · exact block_sound block_209 (by omega) (by omega)
                  · exact block_sound block_210 (by omega) (by omega)
                · by_cases h_212 : k < 108544
                  · exact block_sound block_211 (by omega) (by omega)
                  · exact block_sound block_212 (by omega) (by omega)
              · by_cases h_215 : k < 110080
                · by_cases h_214 : k < 109568
                  · exact block_sound block_213 (by omega) (by omega)
                  · exact block_sound block_214 (by omega) (by omega)
                · by_cases h_216 : k < 110592
                  · exact block_sound block_215 (by omega) (by omega)
                  · exact block_sound block_216 (by omega) (by omega)
        · by_cases h_233 : k < 119296
          · by_cases h_225 : k < 115200
            · by_cases h_221 : k < 113152
              · by_cases h_219 : k < 112128
                · by_cases h_218 : k < 111616
                  · exact block_sound block_217 (by omega) (by omega)
                  · exact block_sound block_218 (by omega) (by omega)
                · by_cases h_220 : k < 112640
                  · exact block_sound block_219 (by omega) (by omega)
                  · exact block_sound block_220 (by omega) (by omega)
              · by_cases h_223 : k < 114176
                · by_cases h_222 : k < 113664
                  · exact block_sound block_221 (by omega) (by omega)
                  · exact block_sound block_222 (by omega) (by omega)
                · by_cases h_224 : k < 114688
                  · exact block_sound block_223 (by omega) (by omega)
                  · exact block_sound block_224 (by omega) (by omega)
            · by_cases h_229 : k < 117248
              · by_cases h_227 : k < 116224
                · by_cases h_226 : k < 115712
                  · exact block_sound block_225 (by omega) (by omega)
                  · exact block_sound block_226 (by omega) (by omega)
                · by_cases h_228 : k < 116736
                  · exact block_sound block_227 (by omega) (by omega)
                  · exact block_sound block_228 (by omega) (by omega)
              · by_cases h_231 : k < 118272
                · by_cases h_230 : k < 117760
                  · exact block_sound block_229 (by omega) (by omega)
                  · exact block_sound block_230 (by omega) (by omega)
                · by_cases h_232 : k < 118784
                  · exact block_sound block_231 (by omega) (by omega)
                  · exact block_sound block_232 (by omega) (by omega)
          · by_cases h_241 : k < 123392
            · by_cases h_237 : k < 121344
              · by_cases h_235 : k < 120320
                · by_cases h_234 : k < 119808
                  · exact block_sound block_233 (by omega) (by omega)
                  · exact block_sound block_234 (by omega) (by omega)
                · by_cases h_236 : k < 120832
                  · exact block_sound block_235 (by omega) (by omega)
                  · exact block_sound block_236 (by omega) (by omega)
              · by_cases h_239 : k < 122368
                · by_cases h_238 : k < 121856
                  · exact block_sound block_237 (by omega) (by omega)
                  · exact block_sound block_238 (by omega) (by omega)
                · by_cases h_240 : k < 122880
                  · exact block_sound block_239 (by omega) (by omega)
                  · exact block_sound block_240 (by omega) (by omega)
            · by_cases h_245 : k < 125440
              · by_cases h_243 : k < 124416
                · by_cases h_242 : k < 123904
                  · exact block_sound block_241 (by omega) (by omega)
                  · exact block_sound block_242 (by omega) (by omega)
                · by_cases h_244 : k < 124928
                  · exact block_sound block_243 (by omega) (by omega)
                  · exact block_sound block_244 (by omega) (by omega)
              · by_cases h_247 : k < 126464
                · by_cases h_246 : k < 125952
                  · exact block_sound block_245 (by omega) (by omega)
                  · exact block_sound block_246 (by omega) (by omega)
                · by_cases h_248 : k < 126976
                  · exact block_sound block_247 (by omega) (by omega)
                  · exact block_sound block_248 (by omega) (by omega)
  · by_cases h_374 : k < 191488
    · by_cases h_311 : k < 159232
      · by_cases h_280 : k < 143360
        · by_cases h_264 : k < 135168
          · by_cases h_256 : k < 131072
            · by_cases h_252 : k < 129024
              · by_cases h_250 : k < 128000
                · exact block_sound block_249 (by omega) (by omega)
                · by_cases h_251 : k < 128512
                  · exact block_sound block_250 (by omega) (by omega)
                  · exact block_sound block_251 (by omega) (by omega)
              · by_cases h_254 : k < 130048
                · by_cases h_253 : k < 129536
                  · exact block_sound block_252 (by omega) (by omega)
                  · exact block_sound block_253 (by omega) (by omega)
                · by_cases h_255 : k < 130560
                  · exact block_sound block_254 (by omega) (by omega)
                  · exact block_sound block_255 (by omega) (by omega)
            · by_cases h_260 : k < 133120
              · by_cases h_258 : k < 132096
                · by_cases h_257 : k < 131584
                  · exact block_sound block_256 (by omega) (by omega)
                  · exact block_sound block_257 (by omega) (by omega)
                · by_cases h_259 : k < 132608
                  · exact block_sound block_258 (by omega) (by omega)
                  · exact block_sound block_259 (by omega) (by omega)
              · by_cases h_262 : k < 134144
                · by_cases h_261 : k < 133632
                  · exact block_sound block_260 (by omega) (by omega)
                  · exact block_sound block_261 (by omega) (by omega)
                · by_cases h_263 : k < 134656
                  · exact block_sound block_262 (by omega) (by omega)
                  · exact block_sound block_263 (by omega) (by omega)
          · by_cases h_272 : k < 139264
            · by_cases h_268 : k < 137216
              · by_cases h_266 : k < 136192
                · by_cases h_265 : k < 135680
                  · exact block_sound block_264 (by omega) (by omega)
                  · exact block_sound block_265 (by omega) (by omega)
                · by_cases h_267 : k < 136704
                  · exact block_sound block_266 (by omega) (by omega)
                  · exact block_sound block_267 (by omega) (by omega)
              · by_cases h_270 : k < 138240
                · by_cases h_269 : k < 137728
                  · exact block_sound block_268 (by omega) (by omega)
                  · exact block_sound block_269 (by omega) (by omega)
                · by_cases h_271 : k < 138752
                  · exact block_sound block_270 (by omega) (by omega)
                  · exact block_sound block_271 (by omega) (by omega)
            · by_cases h_276 : k < 141312
              · by_cases h_274 : k < 140288
                · by_cases h_273 : k < 139776
                  · exact block_sound block_272 (by omega) (by omega)
                  · exact block_sound block_273 (by omega) (by omega)
                · by_cases h_275 : k < 140800
                  · exact block_sound block_274 (by omega) (by omega)
                  · exact block_sound block_275 (by omega) (by omega)
              · by_cases h_278 : k < 142336
                · by_cases h_277 : k < 141824
                  · exact block_sound block_276 (by omega) (by omega)
                  · exact block_sound block_277 (by omega) (by omega)
                · by_cases h_279 : k < 142848
                  · exact block_sound block_278 (by omega) (by omega)
                  · exact block_sound block_279 (by omega) (by omega)
        · by_cases h_295 : k < 151040
          · by_cases h_287 : k < 146944
            · by_cases h_283 : k < 144896
              · by_cases h_281 : k < 143872
                · exact block_sound block_280 (by omega) (by omega)
                · by_cases h_282 : k < 144384
                  · exact block_sound block_281 (by omega) (by omega)
                  · exact block_sound block_282 (by omega) (by omega)
              · by_cases h_285 : k < 145920
                · by_cases h_284 : k < 145408
                  · exact block_sound block_283 (by omega) (by omega)
                  · exact block_sound block_284 (by omega) (by omega)
                · by_cases h_286 : k < 146432
                  · exact block_sound block_285 (by omega) (by omega)
                  · exact block_sound block_286 (by omega) (by omega)
            · by_cases h_291 : k < 148992
              · by_cases h_289 : k < 147968
                · by_cases h_288 : k < 147456
                  · exact block_sound block_287 (by omega) (by omega)
                  · exact block_sound block_288 (by omega) (by omega)
                · by_cases h_290 : k < 148480
                  · exact block_sound block_289 (by omega) (by omega)
                  · exact block_sound block_290 (by omega) (by omega)
              · by_cases h_293 : k < 150016
                · by_cases h_292 : k < 149504
                  · exact block_sound block_291 (by omega) (by omega)
                  · exact block_sound block_292 (by omega) (by omega)
                · by_cases h_294 : k < 150528
                  · exact block_sound block_293 (by omega) (by omega)
                  · exact block_sound block_294 (by omega) (by omega)
          · by_cases h_303 : k < 155136
            · by_cases h_299 : k < 153088
              · by_cases h_297 : k < 152064
                · by_cases h_296 : k < 151552
                  · exact block_sound block_295 (by omega) (by omega)
                  · exact block_sound block_296 (by omega) (by omega)
                · by_cases h_298 : k < 152576
                  · exact block_sound block_297 (by omega) (by omega)
                  · exact block_sound block_298 (by omega) (by omega)
              · by_cases h_301 : k < 154112
                · by_cases h_300 : k < 153600
                  · exact block_sound block_299 (by omega) (by omega)
                  · exact block_sound block_300 (by omega) (by omega)
                · by_cases h_302 : k < 154624
                  · exact block_sound block_301 (by omega) (by omega)
                  · exact block_sound block_302 (by omega) (by omega)
            · by_cases h_307 : k < 157184
              · by_cases h_305 : k < 156160
                · by_cases h_304 : k < 155648
                  · exact block_sound block_303 (by omega) (by omega)
                  · exact block_sound block_304 (by omega) (by omega)
                · by_cases h_306 : k < 156672
                  · exact block_sound block_305 (by omega) (by omega)
                  · exact block_sound block_306 (by omega) (by omega)
              · by_cases h_309 : k < 158208
                · by_cases h_308 : k < 157696
                  · exact block_sound block_307 (by omega) (by omega)
                  · exact block_sound block_308 (by omega) (by omega)
                · by_cases h_310 : k < 158720
                  · exact block_sound block_309 (by omega) (by omega)
                  · exact block_sound block_310 (by omega) (by omega)
      · by_cases h_342 : k < 175104
        · by_cases h_326 : k < 166912
          · by_cases h_318 : k < 162816
            · by_cases h_314 : k < 160768
              · by_cases h_312 : k < 159744
                · exact block_sound block_311 (by omega) (by omega)
                · by_cases h_313 : k < 160256
                  · exact block_sound block_312 (by omega) (by omega)
                  · exact block_sound block_313 (by omega) (by omega)
              · by_cases h_316 : k < 161792
                · by_cases h_315 : k < 161280
                  · exact block_sound block_314 (by omega) (by omega)
                  · exact block_sound block_315 (by omega) (by omega)
                · by_cases h_317 : k < 162304
                  · exact block_sound block_316 (by omega) (by omega)
                  · exact block_sound block_317 (by omega) (by omega)
            · by_cases h_322 : k < 164864
              · by_cases h_320 : k < 163840
                · by_cases h_319 : k < 163328
                  · exact block_sound block_318 (by omega) (by omega)
                  · exact block_sound block_319 (by omega) (by omega)
                · by_cases h_321 : k < 164352
                  · exact block_sound block_320 (by omega) (by omega)
                  · exact block_sound block_321 (by omega) (by omega)
              · by_cases h_324 : k < 165888
                · by_cases h_323 : k < 165376
                  · exact block_sound block_322 (by omega) (by omega)
                  · exact block_sound block_323 (by omega) (by omega)
                · by_cases h_325 : k < 166400
                  · exact block_sound block_324 (by omega) (by omega)
                  · exact block_sound block_325 (by omega) (by omega)
          · by_cases h_334 : k < 171008
            · by_cases h_330 : k < 168960
              · by_cases h_328 : k < 167936
                · by_cases h_327 : k < 167424
                  · exact block_sound block_326 (by omega) (by omega)
                  · exact block_sound block_327 (by omega) (by omega)
                · by_cases h_329 : k < 168448
                  · exact block_sound block_328 (by omega) (by omega)
                  · exact block_sound block_329 (by omega) (by omega)
              · by_cases h_332 : k < 169984
                · by_cases h_331 : k < 169472
                  · exact block_sound block_330 (by omega) (by omega)
                  · exact block_sound block_331 (by omega) (by omega)
                · by_cases h_333 : k < 170496
                  · exact block_sound block_332 (by omega) (by omega)
                  · exact block_sound block_333 (by omega) (by omega)
            · by_cases h_338 : k < 173056
              · by_cases h_336 : k < 172032
                · by_cases h_335 : k < 171520
                  · exact block_sound block_334 (by omega) (by omega)
                  · exact block_sound block_335 (by omega) (by omega)
                · by_cases h_337 : k < 172544
                  · exact block_sound block_336 (by omega) (by omega)
                  · exact block_sound block_337 (by omega) (by omega)
              · by_cases h_340 : k < 174080
                · by_cases h_339 : k < 173568
                  · exact block_sound block_338 (by omega) (by omega)
                  · exact block_sound block_339 (by omega) (by omega)
                · by_cases h_341 : k < 174592
                  · exact block_sound block_340 (by omega) (by omega)
                  · exact block_sound block_341 (by omega) (by omega)
        · by_cases h_358 : k < 183296
          · by_cases h_350 : k < 179200
            · by_cases h_346 : k < 177152
              · by_cases h_344 : k < 176128
                · by_cases h_343 : k < 175616
                  · exact block_sound block_342 (by omega) (by omega)
                  · exact block_sound block_343 (by omega) (by omega)
                · by_cases h_345 : k < 176640
                  · exact block_sound block_344 (by omega) (by omega)
                  · exact block_sound block_345 (by omega) (by omega)
              · by_cases h_348 : k < 178176
                · by_cases h_347 : k < 177664
                  · exact block_sound block_346 (by omega) (by omega)
                  · exact block_sound block_347 (by omega) (by omega)
                · by_cases h_349 : k < 178688
                  · exact block_sound block_348 (by omega) (by omega)
                  · exact block_sound block_349 (by omega) (by omega)
            · by_cases h_354 : k < 181248
              · by_cases h_352 : k < 180224
                · by_cases h_351 : k < 179712
                  · exact block_sound block_350 (by omega) (by omega)
                  · exact block_sound block_351 (by omega) (by omega)
                · by_cases h_353 : k < 180736
                  · exact block_sound block_352 (by omega) (by omega)
                  · exact block_sound block_353 (by omega) (by omega)
              · by_cases h_356 : k < 182272
                · by_cases h_355 : k < 181760
                  · exact block_sound block_354 (by omega) (by omega)
                  · exact block_sound block_355 (by omega) (by omega)
                · by_cases h_357 : k < 182784
                  · exact block_sound block_356 (by omega) (by omega)
                  · exact block_sound block_357 (by omega) (by omega)
          · by_cases h_366 : k < 187392
            · by_cases h_362 : k < 185344
              · by_cases h_360 : k < 184320
                · by_cases h_359 : k < 183808
                  · exact block_sound block_358 (by omega) (by omega)
                  · exact block_sound block_359 (by omega) (by omega)
                · by_cases h_361 : k < 184832
                  · exact block_sound block_360 (by omega) (by omega)
                  · exact block_sound block_361 (by omega) (by omega)
              · by_cases h_364 : k < 186368
                · by_cases h_363 : k < 185856
                  · exact block_sound block_362 (by omega) (by omega)
                  · exact block_sound block_363 (by omega) (by omega)
                · by_cases h_365 : k < 186880
                  · exact block_sound block_364 (by omega) (by omega)
                  · exact block_sound block_365 (by omega) (by omega)
            · by_cases h_370 : k < 189440
              · by_cases h_368 : k < 188416
                · by_cases h_367 : k < 187904
                  · exact block_sound block_366 (by omega) (by omega)
                  · exact block_sound block_367 (by omega) (by omega)
                · by_cases h_369 : k < 188928
                  · exact block_sound block_368 (by omega) (by omega)
                  · exact block_sound block_369 (by omega) (by omega)
              · by_cases h_372 : k < 190464
                · by_cases h_371 : k < 189952
                  · exact block_sound block_370 (by omega) (by omega)
                  · exact block_sound block_371 (by omega) (by omega)
                · by_cases h_373 : k < 190976
                  · exact block_sound block_372 (by omega) (by omega)
                  · exact block_sound block_373 (by omega) (by omega)
    · by_cases h_436 : k < 223232
      · by_cases h_405 : k < 207360
        · by_cases h_389 : k < 199168
          · by_cases h_381 : k < 195072
            · by_cases h_377 : k < 193024
              · by_cases h_375 : k < 192000
                · exact block_sound block_374 (by omega) (by omega)
                · by_cases h_376 : k < 192512
                  · exact block_sound block_375 (by omega) (by omega)
                  · exact block_sound block_376 (by omega) (by omega)
              · by_cases h_379 : k < 194048
                · by_cases h_378 : k < 193536
                  · exact block_sound block_377 (by omega) (by omega)
                  · exact block_sound block_378 (by omega) (by omega)
                · by_cases h_380 : k < 194560
                  · exact block_sound block_379 (by omega) (by omega)
                  · exact block_sound block_380 (by omega) (by omega)
            · by_cases h_385 : k < 197120
              · by_cases h_383 : k < 196096
                · by_cases h_382 : k < 195584
                  · exact block_sound block_381 (by omega) (by omega)
                  · exact block_sound block_382 (by omega) (by omega)
                · by_cases h_384 : k < 196608
                  · exact block_sound block_383 (by omega) (by omega)
                  · exact block_sound block_384 (by omega) (by omega)
              · by_cases h_387 : k < 198144
                · by_cases h_386 : k < 197632
                  · exact block_sound block_385 (by omega) (by omega)
                  · exact block_sound block_386 (by omega) (by omega)
                · by_cases h_388 : k < 198656
                  · exact block_sound block_387 (by omega) (by omega)
                  · exact block_sound block_388 (by omega) (by omega)
          · by_cases h_397 : k < 203264
            · by_cases h_393 : k < 201216
              · by_cases h_391 : k < 200192
                · by_cases h_390 : k < 199680
                  · exact block_sound block_389 (by omega) (by omega)
                  · exact block_sound block_390 (by omega) (by omega)
                · by_cases h_392 : k < 200704
                  · exact block_sound block_391 (by omega) (by omega)
                  · exact block_sound block_392 (by omega) (by omega)
              · by_cases h_395 : k < 202240
                · by_cases h_394 : k < 201728
                  · exact block_sound block_393 (by omega) (by omega)
                  · exact block_sound block_394 (by omega) (by omega)
                · by_cases h_396 : k < 202752
                  · exact block_sound block_395 (by omega) (by omega)
                  · exact block_sound block_396 (by omega) (by omega)
            · by_cases h_401 : k < 205312
              · by_cases h_399 : k < 204288
                · by_cases h_398 : k < 203776
                  · exact block_sound block_397 (by omega) (by omega)
                  · exact block_sound block_398 (by omega) (by omega)
                · by_cases h_400 : k < 204800
                  · exact block_sound block_399 (by omega) (by omega)
                  · exact block_sound block_400 (by omega) (by omega)
              · by_cases h_403 : k < 206336
                · by_cases h_402 : k < 205824
                  · exact block_sound block_401 (by omega) (by omega)
                  · exact block_sound block_402 (by omega) (by omega)
                · by_cases h_404 : k < 206848
                  · exact block_sound block_403 (by omega) (by omega)
                  · exact block_sound block_404 (by omega) (by omega)
        · by_cases h_420 : k < 215040
          · by_cases h_412 : k < 210944
            · by_cases h_408 : k < 208896
              · by_cases h_406 : k < 207872
                · exact block_sound block_405 (by omega) (by omega)
                · by_cases h_407 : k < 208384
                  · exact block_sound block_406 (by omega) (by omega)
                  · exact block_sound block_407 (by omega) (by omega)
              · by_cases h_410 : k < 209920
                · by_cases h_409 : k < 209408
                  · exact block_sound block_408 (by omega) (by omega)
                  · exact block_sound block_409 (by omega) (by omega)
                · by_cases h_411 : k < 210432
                  · exact block_sound block_410 (by omega) (by omega)
                  · exact block_sound block_411 (by omega) (by omega)
            · by_cases h_416 : k < 212992
              · by_cases h_414 : k < 211968
                · by_cases h_413 : k < 211456
                  · exact block_sound block_412 (by omega) (by omega)
                  · exact block_sound block_413 (by omega) (by omega)
                · by_cases h_415 : k < 212480
                  · exact block_sound block_414 (by omega) (by omega)
                  · exact block_sound block_415 (by omega) (by omega)
              · by_cases h_418 : k < 214016
                · by_cases h_417 : k < 213504
                  · exact block_sound block_416 (by omega) (by omega)
                  · exact block_sound block_417 (by omega) (by omega)
                · by_cases h_419 : k < 214528
                  · exact block_sound block_418 (by omega) (by omega)
                  · exact block_sound block_419 (by omega) (by omega)
          · by_cases h_428 : k < 219136
            · by_cases h_424 : k < 217088
              · by_cases h_422 : k < 216064
                · by_cases h_421 : k < 215552
                  · exact block_sound block_420 (by omega) (by omega)
                  · exact block_sound block_421 (by omega) (by omega)
                · by_cases h_423 : k < 216576
                  · exact block_sound block_422 (by omega) (by omega)
                  · exact block_sound block_423 (by omega) (by omega)
              · by_cases h_426 : k < 218112
                · by_cases h_425 : k < 217600
                  · exact block_sound block_424 (by omega) (by omega)
                  · exact block_sound block_425 (by omega) (by omega)
                · by_cases h_427 : k < 218624
                  · exact block_sound block_426 (by omega) (by omega)
                  · exact block_sound block_427 (by omega) (by omega)
            · by_cases h_432 : k < 221184
              · by_cases h_430 : k < 220160
                · by_cases h_429 : k < 219648
                  · exact block_sound block_428 (by omega) (by omega)
                  · exact block_sound block_429 (by omega) (by omega)
                · by_cases h_431 : k < 220672
                  · exact block_sound block_430 (by omega) (by omega)
                  · exact block_sound block_431 (by omega) (by omega)
              · by_cases h_434 : k < 222208
                · by_cases h_433 : k < 221696
                  · exact block_sound block_432 (by omega) (by omega)
                  · exact block_sound block_433 (by omega) (by omega)
                · by_cases h_435 : k < 222720
                  · exact block_sound block_434 (by omega) (by omega)
                  · exact block_sound block_435 (by omega) (by omega)
      · by_cases h_467 : k < 239104
        · by_cases h_451 : k < 230912
          · by_cases h_443 : k < 226816
            · by_cases h_439 : k < 224768
              · by_cases h_437 : k < 223744
                · exact block_sound block_436 (by omega) (by omega)
                · by_cases h_438 : k < 224256
                  · exact block_sound block_437 (by omega) (by omega)
                  · exact block_sound block_438 (by omega) (by omega)
              · by_cases h_441 : k < 225792
                · by_cases h_440 : k < 225280
                  · exact block_sound block_439 (by omega) (by omega)
                  · exact block_sound block_440 (by omega) (by omega)
                · by_cases h_442 : k < 226304
                  · exact block_sound block_441 (by omega) (by omega)
                  · exact block_sound block_442 (by omega) (by omega)
            · by_cases h_447 : k < 228864
              · by_cases h_445 : k < 227840
                · by_cases h_444 : k < 227328
                  · exact block_sound block_443 (by omega) (by omega)
                  · exact block_sound block_444 (by omega) (by omega)
                · by_cases h_446 : k < 228352
                  · exact block_sound block_445 (by omega) (by omega)
                  · exact block_sound block_446 (by omega) (by omega)
              · by_cases h_449 : k < 229888
                · by_cases h_448 : k < 229376
                  · exact block_sound block_447 (by omega) (by omega)
                  · exact block_sound block_448 (by omega) (by omega)
                · by_cases h_450 : k < 230400
                  · exact block_sound block_449 (by omega) (by omega)
                  · exact block_sound block_450 (by omega) (by omega)
          · by_cases h_459 : k < 235008
            · by_cases h_455 : k < 232960
              · by_cases h_453 : k < 231936
                · by_cases h_452 : k < 231424
                  · exact block_sound block_451 (by omega) (by omega)
                  · exact block_sound block_452 (by omega) (by omega)
                · by_cases h_454 : k < 232448
                  · exact block_sound block_453 (by omega) (by omega)
                  · exact block_sound block_454 (by omega) (by omega)
              · by_cases h_457 : k < 233984
                · by_cases h_456 : k < 233472
                  · exact block_sound block_455 (by omega) (by omega)
                  · exact block_sound block_456 (by omega) (by omega)
                · by_cases h_458 : k < 234496
                  · exact block_sound block_457 (by omega) (by omega)
                  · exact block_sound block_458 (by omega) (by omega)
            · by_cases h_463 : k < 237056
              · by_cases h_461 : k < 236032
                · by_cases h_460 : k < 235520
                  · exact block_sound block_459 (by omega) (by omega)
                  · exact block_sound block_460 (by omega) (by omega)
                · by_cases h_462 : k < 236544
                  · exact block_sound block_461 (by omega) (by omega)
                  · exact block_sound block_462 (by omega) (by omega)
              · by_cases h_465 : k < 238080
                · by_cases h_464 : k < 237568
                  · exact block_sound block_463 (by omega) (by omega)
                  · exact block_sound block_464 (by omega) (by omega)
                · by_cases h_466 : k < 238592
                  · exact block_sound block_465 (by omega) (by omega)
                  · exact block_sound block_466 (by omega) (by omega)
        · by_cases h_483 : k < 247296
          · by_cases h_475 : k < 243200
            · by_cases h_471 : k < 241152
              · by_cases h_469 : k < 240128
                · by_cases h_468 : k < 239616
                  · exact block_sound block_467 (by omega) (by omega)
                  · exact block_sound block_468 (by omega) (by omega)
                · by_cases h_470 : k < 240640
                  · exact block_sound block_469 (by omega) (by omega)
                  · exact block_sound block_470 (by omega) (by omega)
              · by_cases h_473 : k < 242176
                · by_cases h_472 : k < 241664
                  · exact block_sound block_471 (by omega) (by omega)
                  · exact block_sound block_472 (by omega) (by omega)
                · by_cases h_474 : k < 242688
                  · exact block_sound block_473 (by omega) (by omega)
                  · exact block_sound block_474 (by omega) (by omega)
            · by_cases h_479 : k < 245248
              · by_cases h_477 : k < 244224
                · by_cases h_476 : k < 243712
                  · exact block_sound block_475 (by omega) (by omega)
                  · exact block_sound block_476 (by omega) (by omega)
                · by_cases h_478 : k < 244736
                  · exact block_sound block_477 (by omega) (by omega)
                  · exact block_sound block_478 (by omega) (by omega)
              · by_cases h_481 : k < 246272
                · by_cases h_480 : k < 245760
                  · exact block_sound block_479 (by omega) (by omega)
                  · exact block_sound block_480 (by omega) (by omega)
                · by_cases h_482 : k < 246784
                  · exact block_sound block_481 (by omega) (by omega)
                  · exact block_sound block_482 (by omega) (by omega)
          · by_cases h_491 : k < 251392
            · by_cases h_487 : k < 249344
              · by_cases h_485 : k < 248320
                · by_cases h_484 : k < 247808
                  · exact block_sound block_483 (by omega) (by omega)
                  · exact block_sound block_484 (by omega) (by omega)
                · by_cases h_486 : k < 248832
                  · exact block_sound block_485 (by omega) (by omega)
                  · exact block_sound block_486 (by omega) (by omega)
              · by_cases h_489 : k < 250368
                · by_cases h_488 : k < 249856
                  · exact block_sound block_487 (by omega) (by omega)
                  · exact block_sound block_488 (by omega) (by omega)
                · by_cases h_490 : k < 250880
                  · exact block_sound block_489 (by omega) (by omega)
                  · exact block_sound block_490 (by omega) (by omega)
            · by_cases h_495 : k < 253440
              · by_cases h_493 : k < 252416
                · by_cases h_492 : k < 251904
                  · exact block_sound block_491 (by omega) (by omega)
                  · exact block_sound block_492 (by omega) (by omega)
                · by_cases h_494 : k < 252928
                  · exact block_sound block_493 (by omega) (by omega)
                  · exact block_sound block_494 (by omega) (by omega)
              · by_cases h_497 : k < 254464
                · by_cases h_496 : k < 253952
                  · exact block_sound block_495 (by omega) (by omega)
                  · exact block_sound block_496 (by omega) (by omega)
                · by_cases h_498 : k < 254976
                  · exact block_sound block_497 (by omega) (by omega)
                  · exact block_sound block_498 (by omega) (by omega)

theorem Conjectures.Goldbach.FiniteResidueRough510510 :
  ∀ a : ℕ, a < 510510 → Even a → ∃ p ∈ ({3,5,7,11,41,61,79,149,167,769,1747,2297,2311} : Finset ℕ), Nat.Coprime ((a+510510-p)%510510) 510510 := by
  intro a ha he
  obtain ⟨k, rfl⟩ := he
  obtain ⟨p, hp, h⟩ := List.any_eq_true.mp (all_covered k (by omega))
  refine ⟨p, ?_, ?_⟩
  · simpa [candidates] using hp
  · change Nat.gcd _ _ = 1
    rw [← Nat.gcd_rec 510510, Nat.gcd_comm 510510]
    simpa [two_mul] using (beq_iff_eq.mp h)
